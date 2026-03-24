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
static const lean_ctor_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 1),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
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
lean_inc(v___y_168_);
v___x_174_ = lean_apply_5(v_x_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, lean_box(0));
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_a_173_);
lean_dec(v___y_170_);
lean_dec(v___y_168_);
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
lean_dec(v___y_170_);
lean_dec(v___y_168_);
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
lean_dec(v___y_170_);
lean_dec(v___y_168_);
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
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
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
lean_object* v_fileName_354_; lean_object* v_fileMap_355_; lean_object* v_options_356_; lean_object* v_currRecDepth_357_; lean_object* v_maxRecDepth_358_; lean_object* v_ref_359_; lean_object* v_currNamespace_360_; lean_object* v_openDecls_361_; lean_object* v_initHeartbeats_362_; lean_object* v_maxHeartbeats_363_; lean_object* v_quotContext_364_; lean_object* v_currMacroScope_365_; uint8_t v_diag_366_; lean_object* v_cancelTk_x3f_367_; uint8_t v_suppressElabErrors_368_; lean_object* v_inheritedTraceOptions_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_424_; 
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
v_isSharedCheck_424_ = !lean_is_exclusive(v___y_351_);
if (v_isSharedCheck_424_ == 0)
{
v___x_371_ = v___y_351_;
v_isShared_372_ = v_isSharedCheck_424_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_inheritedTraceOptions_369_);
lean_inc(v_cancelTk_x3f_367_);
lean_inc(v_currMacroScope_365_);
lean_inc(v_quotContext_364_);
lean_inc(v_maxHeartbeats_363_);
lean_inc(v_initHeartbeats_362_);
lean_inc(v_openDecls_361_);
lean_inc(v_currNamespace_360_);
lean_inc(v_ref_359_);
lean_inc(v_maxRecDepth_358_);
lean_inc(v_currRecDepth_357_);
lean_inc(v_options_356_);
lean_inc(v_fileMap_355_);
lean_inc(v_fileName_354_);
lean_dec(v___y_351_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_424_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v_traceState_374_; lean_object* v_traces_375_; lean_object* v_ref_376_; lean_object* v___x_378_; 
v___x_373_ = lean_st_ref_get(v___y_352_);
v_traceState_374_ = lean_ctor_get(v___x_373_, 4);
lean_inc_ref(v_traceState_374_);
lean_dec(v___x_373_);
v_traces_375_ = lean_ctor_get(v_traceState_374_, 0);
lean_inc_ref(v_traces_375_);
lean_dec_ref(v_traceState_374_);
v_ref_376_ = l_Lean_replaceRef(v_ref_347_, v_ref_359_);
lean_dec(v_ref_359_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 5, v_ref_376_);
v___x_378_ = v___x_371_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_fileName_354_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_fileMap_355_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_options_356_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_currRecDepth_357_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_maxRecDepth_358_);
lean_ctor_set(v_reuseFailAlloc_423_, 5, v_ref_376_);
lean_ctor_set(v_reuseFailAlloc_423_, 6, v_currNamespace_360_);
lean_ctor_set(v_reuseFailAlloc_423_, 7, v_openDecls_361_);
lean_ctor_set(v_reuseFailAlloc_423_, 8, v_initHeartbeats_362_);
lean_ctor_set(v_reuseFailAlloc_423_, 9, v_maxHeartbeats_363_);
lean_ctor_set(v_reuseFailAlloc_423_, 10, v_quotContext_364_);
lean_ctor_set(v_reuseFailAlloc_423_, 11, v_currMacroScope_365_);
lean_ctor_set(v_reuseFailAlloc_423_, 12, v_cancelTk_x3f_367_);
lean_ctor_set(v_reuseFailAlloc_423_, 13, v_inheritedTraceOptions_369_);
lean_ctor_set_uint8(v_reuseFailAlloc_423_, sizeof(void*)*14, v_diag_366_);
lean_ctor_set_uint8(v_reuseFailAlloc_423_, sizeof(void*)*14 + 1, v_suppressElabErrors_368_);
v___x_378_ = v_reuseFailAlloc_423_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; size_t v_sz_380_; size_t v___x_381_; lean_object* v___x_382_; lean_object* v_msg_383_; lean_object* v___x_384_; lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_422_; 
v___x_379_ = l_Lean_PersistentArray_toArray___redArg(v_traces_375_);
lean_dec_ref(v_traces_375_);
v_sz_380_ = lean_array_size(v___x_379_);
v___x_381_ = ((size_t)0ULL);
v___x_382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__7(v_sz_380_, v___x_381_, v___x_379_);
v_msg_383_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_383_, 0, v_data_346_);
lean_ctor_set(v_msg_383_, 1, v_msg_348_);
lean_ctor_set(v_msg_383_, 2, v___x_382_);
v___x_384_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__8(v_msg_383_, v___y_349_, v___y_350_, v___x_378_, v___y_352_);
lean_dec_ref(v___x_378_);
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_422_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_422_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_422_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v_traceState_390_; lean_object* v_env_391_; lean_object* v_nextMacroScope_392_; lean_object* v_ngen_393_; lean_object* v_auxDeclNGen_394_; lean_object* v_cache_395_; lean_object* v_messages_396_; lean_object* v_infoState_397_; lean_object* v_snapshotTasks_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_421_; 
v___x_389_ = lean_st_ref_take(v___y_352_);
v_traceState_390_ = lean_ctor_get(v___x_389_, 4);
v_env_391_ = lean_ctor_get(v___x_389_, 0);
v_nextMacroScope_392_ = lean_ctor_get(v___x_389_, 1);
v_ngen_393_ = lean_ctor_get(v___x_389_, 2);
v_auxDeclNGen_394_ = lean_ctor_get(v___x_389_, 3);
v_cache_395_ = lean_ctor_get(v___x_389_, 5);
v_messages_396_ = lean_ctor_get(v___x_389_, 6);
v_infoState_397_ = lean_ctor_get(v___x_389_, 7);
v_snapshotTasks_398_ = lean_ctor_get(v___x_389_, 8);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_421_ == 0)
{
v___x_400_ = v___x_389_;
v_isShared_401_ = v_isSharedCheck_421_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_snapshotTasks_398_);
lean_inc(v_infoState_397_);
lean_inc(v_messages_396_);
lean_inc(v_cache_395_);
lean_inc(v_traceState_390_);
lean_inc(v_auxDeclNGen_394_);
lean_inc(v_ngen_393_);
lean_inc(v_nextMacroScope_392_);
lean_inc(v_env_391_);
lean_dec(v___x_389_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_421_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
uint64_t v_tid_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_419_; 
v_tid_402_ = lean_ctor_get_uint64(v_traceState_390_, sizeof(void*)*1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_traceState_390_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v_traceState_390_, 0);
lean_dec(v_unused_420_);
v___x_404_ = v_traceState_390_;
v_isShared_405_ = v_isSharedCheck_419_;
goto v_resetjp_403_;
}
else
{
lean_dec(v_traceState_390_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_419_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_ref_347_);
lean_ctor_set(v___x_406_, 1, v_a_385_);
v___x_407_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_345_, v___x_406_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_407_);
v___x_409_ = v___x_404_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_407_);
lean_ctor_set_uint64(v_reuseFailAlloc_418_, sizeof(void*)*1, v_tid_402_);
v___x_409_ = v_reuseFailAlloc_418_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_411_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 4, v___x_409_);
v___x_411_ = v___x_400_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_env_391_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_nextMacroScope_392_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_ngen_393_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_auxDeclNGen_394_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_417_, 5, v_cache_395_);
lean_ctor_set(v_reuseFailAlloc_417_, 6, v_messages_396_);
lean_ctor_set(v_reuseFailAlloc_417_, 7, v_infoState_397_);
lean_ctor_set(v_reuseFailAlloc_417_, 8, v_snapshotTasks_398_);
v___x_411_ = v_reuseFailAlloc_417_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_412_ = lean_st_ref_set(v___y_352_, v___x_411_);
v___x_413_ = lean_box(0);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_413_);
v___x_415_ = v___x_387_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5___boxed(lean_object* v_oldTraces_425_, lean_object* v_data_426_, lean_object* v_ref_427_, lean_object* v_msg_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5(v_oldTraces_425_, v_data_426_, v_ref_427_, v_msg_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
return v_res_434_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__1(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__0));
v___x_437_ = l_Lean_stringToMessageData(v___x_436_);
return v___x_437_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__2(void){
_start:
{
lean_object* v___x_438_; double v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_float_of_nat(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__4(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__3));
v___x_442_ = l_Lean_stringToMessageData(v___x_441_);
return v___x_442_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__5(void){
_start:
{
lean_object* v___x_443_; double v___x_444_; 
v___x_443_ = lean_unsigned_to_nat(1000u);
v___x_444_ = lean_float_of_nat(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(lean_object* v_cls_445_, uint8_t v_collapsed_446_, lean_object* v_tag_447_, lean_object* v_opts_448_, uint8_t v_clsEnabled_449_, lean_object* v_oldTraces_450_, lean_object* v_msg_451_, lean_object* v_resStartStop_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_fst_458_; lean_object* v_snd_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_557_; 
v_fst_458_ = lean_ctor_get(v_resStartStop_452_, 0);
v_snd_459_ = lean_ctor_get(v_resStartStop_452_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_resStartStop_452_);
if (v_isSharedCheck_557_ == 0)
{
v___x_461_ = v_resStartStop_452_;
v_isShared_462_ = v_isSharedCheck_557_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_snd_459_);
lean_inc(v_fst_458_);
lean_dec(v_resStartStop_452_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_557_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v_data_466_; lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_556_; 
v_fst_477_ = lean_ctor_get(v_snd_459_, 0);
v_snd_478_ = lean_ctor_get(v_snd_459_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_snd_459_);
if (v_isSharedCheck_556_ == 0)
{
v___x_480_ = v_snd_459_;
v_isShared_481_ = v_isSharedCheck_556_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_snd_478_);
lean_inc(v_fst_477_);
lean_dec(v_snd_459_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_556_;
goto v_resetjp_479_;
}
v___jp_463_:
{
lean_object* v___x_467_; 
v___x_467_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5(v_oldTraces_450_, v_data_466_, v___y_464_, v___y_465_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v___x_468_; 
lean_dec_ref(v___x_467_);
v___x_468_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___redArg(v_fst_458_);
return v___x_468_;
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec(v_fst_458_);
v_a_469_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_467_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_467_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
v_resetjp_479_:
{
lean_object* v___x_482_; uint8_t v___x_483_; lean_object* v___y_485_; lean_object* v_a_486_; uint8_t v___y_510_; double v___y_541_; 
v___x_482_ = l_Lean_trace_profiler;
v___x_483_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v_opts_448_, v___x_482_);
if (v___x_483_ == 0)
{
v___y_510_ = v___x_483_;
goto v___jp_509_;
}
else
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = l_Lean_trace_profiler_useHeartbeats;
v___x_547_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v_opts_448_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; double v___x_550_; double v___x_551_; double v___x_552_; 
v___x_548_ = l_Lean_trace_profiler_threshold;
v___x_549_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__7(v_opts_448_, v___x_548_);
v___x_550_ = lean_float_of_nat(v___x_549_);
v___x_551_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__5);
v___x_552_ = lean_float_div(v___x_550_, v___x_551_);
v___y_541_ = v___x_552_;
goto v___jp_540_;
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; double v___x_555_; 
v___x_553_ = l_Lean_trace_profiler_threshold;
v___x_554_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__7(v_opts_448_, v___x_553_);
v___x_555_ = lean_float_of_nat(v___x_554_);
v___y_541_ = v___x_555_;
goto v___jp_540_;
}
}
v___jp_484_:
{
uint8_t v_result_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v_result_487_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__4(v_fst_458_);
v___x_488_ = l_Lean_TraceResult_toEmoji(v_result_487_);
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
v___x_490_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__1);
if (v_isShared_481_ == 0)
{
lean_ctor_set_tag(v___x_480_, 7);
lean_ctor_set(v___x_480_, 1, v___x_490_);
lean_ctor_set(v___x_480_, 0, v___x_489_);
v___x_492_ = v___x_480_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_503_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v_m_494_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set_tag(v___x_461_, 7);
lean_ctor_set(v___x_461_, 1, v_a_486_);
lean_ctor_set(v___x_461_, 0, v___x_492_);
v_m_494_ = v___x_461_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_a_486_);
v_m_494_ = v_reuseFailAlloc_502_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; double v___x_497_; lean_object* v_data_498_; 
v___x_495_ = lean_box(v_result_487_);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
v___x_497_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__2);
lean_inc_ref(v_tag_447_);
lean_inc_ref(v___x_496_);
lean_inc(v_cls_445_);
v_data_498_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_498_, 0, v_cls_445_);
lean_ctor_set(v_data_498_, 1, v___x_496_);
lean_ctor_set(v_data_498_, 2, v_tag_447_);
lean_ctor_set_float(v_data_498_, sizeof(void*)*3, v___x_497_);
lean_ctor_set_float(v_data_498_, sizeof(void*)*3 + 8, v___x_497_);
lean_ctor_set_uint8(v_data_498_, sizeof(void*)*3 + 16, v_collapsed_446_);
if (v___x_483_ == 0)
{
lean_dec_ref(v___x_496_);
lean_dec(v_snd_478_);
lean_dec(v_fst_477_);
lean_dec_ref(v_tag_447_);
lean_dec(v_cls_445_);
v___y_464_ = v___y_485_;
v___y_465_ = v_m_494_;
v_data_466_ = v_data_498_;
goto v___jp_463_;
}
else
{
lean_object* v_data_499_; double v___x_500_; double v___x_501_; 
lean_dec_ref(v_data_498_);
v_data_499_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_499_, 0, v_cls_445_);
lean_ctor_set(v_data_499_, 1, v___x_496_);
lean_ctor_set(v_data_499_, 2, v_tag_447_);
v___x_500_ = lean_unbox_float(v_fst_477_);
lean_dec(v_fst_477_);
lean_ctor_set_float(v_data_499_, sizeof(void*)*3, v___x_500_);
v___x_501_ = lean_unbox_float(v_snd_478_);
lean_dec(v_snd_478_);
lean_ctor_set_float(v_data_499_, sizeof(void*)*3 + 8, v___x_501_);
lean_ctor_set_uint8(v_data_499_, sizeof(void*)*3 + 16, v_collapsed_446_);
v___y_464_ = v___y_485_;
v___y_465_ = v_m_494_;
v_data_466_ = v_data_499_;
goto v___jp_463_;
}
}
}
}
v___jp_504_:
{
lean_object* v_ref_505_; lean_object* v___x_506_; 
v_ref_505_ = lean_ctor_get(v___y_455_, 5);
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
lean_inc(v___y_454_);
lean_inc_ref(v___y_453_);
lean_inc(v_fst_458_);
v___x_506_ = lean_apply_6(v_msg_451_, v_fst_458_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, lean_box(0));
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v___x_506_);
lean_inc(v_ref_505_);
v___y_485_ = v_ref_505_;
v_a_486_ = v_a_507_;
goto v___jp_484_;
}
else
{
lean_object* v___x_508_; 
lean_dec_ref(v___x_506_);
v___x_508_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__4);
lean_inc(v_ref_505_);
v___y_485_ = v_ref_505_;
v_a_486_ = v___x_508_;
goto v___jp_484_;
}
}
v___jp_509_:
{
if (v_clsEnabled_449_ == 0)
{
if (v___y_510_ == 0)
{
lean_object* v___x_511_; lean_object* v_traceState_512_; lean_object* v_env_513_; lean_object* v_nextMacroScope_514_; lean_object* v_ngen_515_; lean_object* v_auxDeclNGen_516_; lean_object* v_cache_517_; lean_object* v_messages_518_; lean_object* v_infoState_519_; lean_object* v_snapshotTasks_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_539_; 
lean_del_object(v___x_480_);
lean_dec(v_snd_478_);
lean_dec(v_fst_477_);
lean_del_object(v___x_461_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec_ref(v_msg_451_);
lean_dec_ref(v_tag_447_);
lean_dec(v_cls_445_);
v___x_511_ = lean_st_ref_take(v___y_456_);
v_traceState_512_ = lean_ctor_get(v___x_511_, 4);
v_env_513_ = lean_ctor_get(v___x_511_, 0);
v_nextMacroScope_514_ = lean_ctor_get(v___x_511_, 1);
v_ngen_515_ = lean_ctor_get(v___x_511_, 2);
v_auxDeclNGen_516_ = lean_ctor_get(v___x_511_, 3);
v_cache_517_ = lean_ctor_get(v___x_511_, 5);
v_messages_518_ = lean_ctor_get(v___x_511_, 6);
v_infoState_519_ = lean_ctor_get(v___x_511_, 7);
v_snapshotTasks_520_ = lean_ctor_get(v___x_511_, 8);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_539_ == 0)
{
v___x_522_ = v___x_511_;
v_isShared_523_ = v_isSharedCheck_539_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snapshotTasks_520_);
lean_inc(v_infoState_519_);
lean_inc(v_messages_518_);
lean_inc(v_cache_517_);
lean_inc(v_traceState_512_);
lean_inc(v_auxDeclNGen_516_);
lean_inc(v_ngen_515_);
lean_inc(v_nextMacroScope_514_);
lean_inc(v_env_513_);
lean_dec(v___x_511_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_539_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
uint64_t v_tid_524_; lean_object* v_traces_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_538_; 
v_tid_524_ = lean_ctor_get_uint64(v_traceState_512_, sizeof(void*)*1);
v_traces_525_ = lean_ctor_get(v_traceState_512_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v_traceState_512_);
if (v_isSharedCheck_538_ == 0)
{
v___x_527_ = v_traceState_512_;
v_isShared_528_ = v_isSharedCheck_538_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_traces_525_);
lean_dec(v_traceState_512_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_538_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_450_, v_traces_525_);
lean_dec_ref(v_traces_525_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_529_);
lean_ctor_set_uint64(v_reuseFailAlloc_537_, sizeof(void*)*1, v_tid_524_);
v___x_531_ = v_reuseFailAlloc_537_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_533_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 4, v___x_531_);
v___x_533_ = v___x_522_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_env_513_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_nextMacroScope_514_);
lean_ctor_set(v_reuseFailAlloc_536_, 2, v_ngen_515_);
lean_ctor_set(v_reuseFailAlloc_536_, 3, v_auxDeclNGen_516_);
lean_ctor_set(v_reuseFailAlloc_536_, 4, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_536_, 5, v_cache_517_);
lean_ctor_set(v_reuseFailAlloc_536_, 6, v_messages_518_);
lean_ctor_set(v_reuseFailAlloc_536_, 7, v_infoState_519_);
lean_ctor_set(v_reuseFailAlloc_536_, 8, v_snapshotTasks_520_);
v___x_533_ = v_reuseFailAlloc_536_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_st_ref_set(v___y_456_, v___x_533_);
lean_dec(v___y_456_);
v___x_535_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___redArg(v_fst_458_);
return v___x_535_;
}
}
}
}
}
else
{
goto v___jp_504_;
}
}
else
{
goto v___jp_504_;
}
}
v___jp_540_:
{
double v___x_542_; double v___x_543_; double v___x_544_; uint8_t v___x_545_; 
v___x_542_ = lean_unbox_float(v_snd_478_);
v___x_543_ = lean_unbox_float(v_fst_477_);
v___x_544_ = lean_float_sub(v___x_542_, v___x_543_);
v___x_545_ = lean_float_decLt(v___y_541_, v___x_544_);
v___y_510_ = v___x_545_;
goto v___jp_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v_cls_558_, lean_object* v_collapsed_559_, lean_object* v_tag_560_, lean_object* v_opts_561_, lean_object* v_clsEnabled_562_, lean_object* v_oldTraces_563_, lean_object* v_msg_564_, lean_object* v_resStartStop_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
uint8_t v_collapsed_boxed_571_; uint8_t v_clsEnabled_boxed_572_; lean_object* v_res_573_; 
v_collapsed_boxed_571_ = lean_unbox(v_collapsed_559_);
v_clsEnabled_boxed_572_ = lean_unbox(v_clsEnabled_562_);
v_res_573_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v_cls_558_, v_collapsed_boxed_571_, v_tag_560_, v_opts_561_, v_clsEnabled_boxed_572_, v_oldTraces_563_, v_msg_564_, v_resStartStop_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec_ref(v_opts_561_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(uint8_t v___x_574_, lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
if (lean_obj_tag(v_x_575_) == 0)
{
lean_object* v___x_582_; 
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v_x_576_);
return v___x_582_;
}
else
{
lean_object* v_head_583_; lean_object* v_tail_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_607_; 
v_head_583_ = lean_ctor_get(v_x_575_, 0);
v_tail_584_ = lean_ctor_get(v_x_575_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v_x_575_);
if (v_isSharedCheck_607_ == 0)
{
v___x_586_ = v_x_575_;
v_isShared_587_ = v_isSharedCheck_607_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_tail_584_);
lean_inc(v_head_583_);
lean_dec(v_x_575_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_607_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; 
lean_inc(v___y_580_);
lean_inc_ref(v___y_579_);
lean_inc(v___y_578_);
lean_inc_ref(v___y_577_);
lean_inc(v_head_583_);
v___x_588_ = l_Lean_MVarId_inferInstance(v_head_583_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_dec_ref(v___x_588_);
lean_del_object(v___x_586_);
lean_dec(v_head_583_);
v_x_575_ = v_tail_584_;
goto _start;
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_606_; 
v_a_590_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_606_ == 0)
{
v___x_592_ = v___x_588_;
v_isShared_593_ = v_isSharedCheck_606_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_606_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
uint8_t v___y_595_; uint8_t v___x_604_; 
v___x_604_ = l_Lean_Exception_isInterrupt(v_a_590_);
if (v___x_604_ == 0)
{
uint8_t v___x_605_; 
lean_inc(v_a_590_);
v___x_605_ = l_Lean_Exception_isRuntime(v_a_590_);
v___y_595_ = v___x_605_;
goto v___jp_594_;
}
else
{
v___y_595_ = v___x_604_;
goto v___jp_594_;
}
v___jp_594_:
{
if (v___y_595_ == 0)
{
lean_del_object(v___x_592_);
lean_dec(v_a_590_);
if (v___x_574_ == 0)
{
lean_del_object(v___x_586_);
lean_dec(v_head_583_);
v_x_575_ = v_tail_584_;
goto _start;
}
else
{
lean_object* v___x_598_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_x_576_);
v___x_598_ = v___x_586_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_head_583_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_x_576_);
v___x_598_ = v_reuseFailAlloc_600_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
v_x_575_ = v_tail_584_;
v_x_576_ = v___x_598_;
goto _start;
}
}
}
else
{
lean_object* v___x_602_; 
lean_del_object(v___x_586_);
lean_dec(v_tail_584_);
lean_dec(v_head_583_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v_x_576_);
if (v_isShared_593_ == 0)
{
v___x_602_ = v___x_592_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_590_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object* v___x_608_, lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
uint8_t v___x_14210__boxed_616_; lean_object* v_res_617_; 
v___x_14210__boxed_616_ = lean_unbox(v___x_608_);
v_res_617_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(v___x_14210__boxed_616_, v_x_609_, v_x_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_618_, uint8_t v___x_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
lean_object* v___x_627_; 
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_x_621_);
return v___x_627_;
}
else
{
lean_object* v_head_628_; lean_object* v_tail_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_653_; 
v_head_628_ = lean_ctor_get(v_x_620_, 0);
v_tail_629_ = lean_ctor_get(v_x_620_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_653_ == 0)
{
v___x_631_ = v_x_620_;
v_isShared_632_ = v_isSharedCheck_653_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_tail_629_);
lean_inc(v_head_628_);
lean_dec(v_x_620_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_653_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
uint8_t v_a_634_; lean_object* v___x_640_; 
lean_inc(v___y_625_);
lean_inc_ref(v___y_624_);
lean_inc(v___y_623_);
lean_inc_ref(v___y_622_);
lean_inc(v_head_628_);
v___x_640_ = l_Lean_MVarId_inferInstance(v_head_628_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_dec_ref(v___x_640_);
v_a_634_ = v___x_618_;
goto v___jp_633_;
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_652_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_652_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_652_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_652_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
uint8_t v___y_646_; uint8_t v___x_650_; 
v___x_650_ = l_Lean_Exception_isInterrupt(v_a_641_);
if (v___x_650_ == 0)
{
uint8_t v___x_651_; 
lean_inc(v_a_641_);
v___x_651_ = l_Lean_Exception_isRuntime(v_a_641_);
v___y_646_ = v___x_651_;
goto v___jp_645_;
}
else
{
v___y_646_ = v___x_650_;
goto v___jp_645_;
}
v___jp_645_:
{
if (v___y_646_ == 0)
{
lean_del_object(v___x_643_);
lean_dec(v_a_641_);
v_a_634_ = v___x_619_;
goto v___jp_633_;
}
else
{
lean_object* v___x_648_; 
lean_del_object(v___x_631_);
lean_dec(v_tail_629_);
lean_dec(v_head_628_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v_x_621_);
if (v_isShared_644_ == 0)
{
v___x_648_ = v___x_643_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_641_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
v___jp_633_:
{
if (v_a_634_ == 0)
{
lean_del_object(v___x_631_);
lean_dec(v_head_628_);
v_x_620_ = v_tail_629_;
goto _start;
}
else
{
lean_object* v___x_637_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v_x_621_);
v___x_637_ = v___x_631_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_head_628_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_x_621_);
v___x_637_ = v_reuseFailAlloc_639_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
v_x_620_ = v_tail_629_;
v_x_621_ = v___x_637_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_654_, lean_object* v___x_655_, lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
uint8_t v___x_14287__boxed_663_; uint8_t v___x_14288__boxed_664_; lean_object* v_res_665_; 
v___x_14287__boxed_663_ = lean_unbox(v___x_654_);
v___x_14288__boxed_664_ = lean_unbox(v___x_655_);
v_res_665_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14287__boxed_663_, v___x_14288__boxed_664_, v_x_656_, v_x_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(uint8_t v___x_666_, lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
if (lean_obj_tag(v_x_667_) == 0)
{
lean_object* v___x_674_; 
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v_x_668_);
return v___x_674_;
}
else
{
lean_object* v_head_675_; lean_object* v_tail_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_699_; 
v_head_675_ = lean_ctor_get(v_x_667_, 0);
v_tail_676_ = lean_ctor_get(v_x_667_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_x_667_);
if (v_isSharedCheck_699_ == 0)
{
v___x_678_ = v_x_667_;
v_isShared_679_ = v_isSharedCheck_699_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_tail_676_);
lean_inc(v_head_675_);
lean_dec(v_x_667_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_699_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_685_; 
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
lean_inc(v___y_670_);
lean_inc_ref(v___y_669_);
lean_inc(v_head_675_);
v___x_685_ = l_Lean_MVarId_inferInstance(v_head_675_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_dec_ref(v___x_685_);
if (v___x_666_ == 0)
{
lean_del_object(v___x_678_);
lean_dec(v_head_675_);
v_x_667_ = v_tail_676_;
goto _start;
}
else
{
goto v___jp_680_;
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_698_; 
v_a_687_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_698_ == 0)
{
v___x_689_ = v___x_685_;
v_isShared_690_ = v_isSharedCheck_698_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_685_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_698_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
uint8_t v___y_692_; uint8_t v___x_696_; 
v___x_696_ = l_Lean_Exception_isInterrupt(v_a_687_);
if (v___x_696_ == 0)
{
uint8_t v___x_697_; 
lean_inc(v_a_687_);
v___x_697_ = l_Lean_Exception_isRuntime(v_a_687_);
v___y_692_ = v___x_697_;
goto v___jp_691_;
}
else
{
v___y_692_ = v___x_696_;
goto v___jp_691_;
}
v___jp_691_:
{
if (v___y_692_ == 0)
{
lean_del_object(v___x_689_);
lean_dec(v_a_687_);
goto v___jp_680_;
}
else
{
lean_object* v___x_694_; 
lean_del_object(v___x_678_);
lean_dec(v_tail_676_);
lean_dec(v_head_675_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v_x_668_);
if (v_isShared_690_ == 0)
{
v___x_694_ = v___x_689_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_687_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
v___jp_680_:
{
lean_object* v___x_682_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v_x_668_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_head_675_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_x_668_);
v___x_682_ = v_reuseFailAlloc_684_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
v_x_667_ = v_tail_676_;
v_x_668_ = v___x_682_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object* v___x_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
uint8_t v___x_14369__boxed_708_; lean_object* v_res_709_; 
v___x_14369__boxed_708_ = lean_unbox(v___x_700_);
v_res_709_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v___x_14369__boxed_708_, v_x_701_, v_x_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v_res_709_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_710_; double v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(1000000000u);
v___x_711_ = lean_float_of_nat(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_712_, lean_object* v_g_713_, lean_object* v_e_714_, lean_object* v_cfg_715_, lean_object* v___x_716_, lean_object* v___x_717_, uint8_t v___x_718_, lean_object* v___x_719_, lean_object* v___f_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_options_726_; uint8_t v_hasTrace_727_; 
v_options_726_ = lean_ctor_get(v___y_723_, 2);
v_hasTrace_727_ = lean_ctor_get_uint8(v_options_726_, sizeof(void*)*1);
if (v_hasTrace_727_ == 0)
{
lean_object* v___x_728_; uint8_t v_foApprox_729_; uint8_t v_ctxApprox_730_; uint8_t v_quasiPatternApprox_731_; uint8_t v_constApprox_732_; uint8_t v_isDefEqStuckEx_733_; uint8_t v_unificationHints_734_; uint8_t v_proofIrrelevance_735_; uint8_t v_assignSyntheticOpaque_736_; uint8_t v_offsetCnstrs_737_; uint8_t v_etaStruct_738_; uint8_t v_univApprox_739_; uint8_t v_iota_740_; uint8_t v_beta_741_; uint8_t v_proj_742_; uint8_t v_zeta_743_; uint8_t v_zetaDelta_744_; uint8_t v_zetaUnused_745_; uint8_t v_zetaHave_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v___f_720_);
lean_dec_ref(v___x_719_);
lean_dec(v___x_717_);
v___x_728_ = l_Lean_Meta_Context_config(v___y_721_);
v_foApprox_729_ = lean_ctor_get_uint8(v___x_728_, 0);
v_ctxApprox_730_ = lean_ctor_get_uint8(v___x_728_, 1);
v_quasiPatternApprox_731_ = lean_ctor_get_uint8(v___x_728_, 2);
v_constApprox_732_ = lean_ctor_get_uint8(v___x_728_, 3);
v_isDefEqStuckEx_733_ = lean_ctor_get_uint8(v___x_728_, 4);
v_unificationHints_734_ = lean_ctor_get_uint8(v___x_728_, 5);
v_proofIrrelevance_735_ = lean_ctor_get_uint8(v___x_728_, 6);
v_assignSyntheticOpaque_736_ = lean_ctor_get_uint8(v___x_728_, 7);
v_offsetCnstrs_737_ = lean_ctor_get_uint8(v___x_728_, 8);
v_etaStruct_738_ = lean_ctor_get_uint8(v___x_728_, 10);
v_univApprox_739_ = lean_ctor_get_uint8(v___x_728_, 11);
v_iota_740_ = lean_ctor_get_uint8(v___x_728_, 12);
v_beta_741_ = lean_ctor_get_uint8(v___x_728_, 13);
v_proj_742_ = lean_ctor_get_uint8(v___x_728_, 14);
v_zeta_743_ = lean_ctor_get_uint8(v___x_728_, 15);
v_zetaDelta_744_ = lean_ctor_get_uint8(v___x_728_, 16);
v_zetaUnused_745_ = lean_ctor_get_uint8(v___x_728_, 17);
v_zetaHave_746_ = lean_ctor_get_uint8(v___x_728_, 18);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_784_ == 0)
{
v___x_748_ = v___x_728_;
v_isShared_749_ = v_isSharedCheck_784_;
goto v_resetjp_747_;
}
else
{
lean_dec(v___x_728_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_784_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
uint8_t v_trackZetaDelta_750_; lean_object* v_zetaDeltaSet_751_; lean_object* v_lctx_752_; lean_object* v_localInstances_753_; lean_object* v_defEqCtx_x3f_754_; lean_object* v_synthPendingDepth_755_; lean_object* v_canUnfold_x3f_756_; uint8_t v_univApprox_757_; uint8_t v_inTypeClassResolution_758_; uint8_t v_cacheInferType_759_; lean_object* v_config_761_; 
v_trackZetaDelta_750_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7);
v_zetaDeltaSet_751_ = lean_ctor_get(v___y_721_, 1);
v_lctx_752_ = lean_ctor_get(v___y_721_, 2);
v_localInstances_753_ = lean_ctor_get(v___y_721_, 3);
v_defEqCtx_x3f_754_ = lean_ctor_get(v___y_721_, 4);
v_synthPendingDepth_755_ = lean_ctor_get(v___y_721_, 5);
v_canUnfold_x3f_756_ = lean_ctor_get(v___y_721_, 6);
v_univApprox_757_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_758_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7 + 2);
v_cacheInferType_759_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7 + 3);
if (v_isShared_749_ == 0)
{
v_config_761_ = v___x_748_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 0, v_foApprox_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 1, v_ctxApprox_730_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 2, v_quasiPatternApprox_731_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 3, v_constApprox_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 4, v_isDefEqStuckEx_733_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 5, v_unificationHints_734_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 6, v_proofIrrelevance_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 7, v_assignSyntheticOpaque_736_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 8, v_offsetCnstrs_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 10, v_etaStruct_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 11, v_univApprox_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 12, v_iota_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 13, v_beta_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 14, v_proj_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 15, v_zeta_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 16, v_zetaDelta_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 17, v_zetaUnused_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, 18, v_zetaHave_746_);
v_config_761_ = v_reuseFailAlloc_783_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
uint64_t v___x_762_; uint64_t v___x_763_; uint64_t v___x_764_; uint64_t v___x_765_; uint64_t v___x_766_; uint64_t v_key_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_ctor_set_uint8(v_config_761_, 9, v_transparency_712_);
v___x_762_ = l_Lean_Meta_Context_configKey(v___y_721_);
v___x_763_ = 2ULL;
v___x_764_ = lean_uint64_shift_right(v___x_762_, v___x_763_);
v___x_765_ = lean_uint64_shift_left(v___x_764_, v___x_763_);
v___x_766_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_712_);
v_key_767_ = lean_uint64_lor(v___x_765_, v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_768_, 0, v_config_761_);
lean_ctor_set_uint64(v___x_768_, sizeof(void*)*1, v_key_767_);
lean_inc(v_canUnfold_x3f_756_);
lean_inc(v_synthPendingDepth_755_);
lean_inc(v_defEqCtx_x3f_754_);
lean_inc_ref(v_localInstances_753_);
lean_inc_ref(v_lctx_752_);
lean_inc(v_zetaDeltaSet_751_);
v___x_769_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v_zetaDeltaSet_751_);
lean_ctor_set(v___x_769_, 2, v_lctx_752_);
lean_ctor_set(v___x_769_, 3, v_localInstances_753_);
lean_ctor_set(v___x_769_, 4, v_defEqCtx_x3f_754_);
lean_ctor_set(v___x_769_, 5, v_synthPendingDepth_755_);
lean_ctor_set(v___x_769_, 6, v_canUnfold_x3f_756_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*7, v_trackZetaDelta_750_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*7 + 1, v_univApprox_757_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*7 + 2, v_inTypeClassResolution_758_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*7 + 3, v_cacheInferType_759_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
v___x_770_ = l_Lean_MVarId_apply(v_g_713_, v_e_714_, v_cfg_715_, v___x_716_, v___x_769_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_770_);
v___x_772_ = lean_box(0);
v___x_773_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v_hasTrace_727_, v_a_771_, v___x_772_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_782_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = l_List_reverse___redArg(v_a_774_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
else
{
return v___x_773_;
}
}
else
{
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v___x_770_;
}
}
}
}
else
{
lean_object* v___x_785_; lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_1024_; 
lean_inc(v___x_717_);
v___x_785_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg(v___x_717_, v___y_723_);
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_1024_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_1024_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v_a_793_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v_a_809_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v_a_829_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v_a_842_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; uint8_t v___x_964_; 
v___x_964_ = lean_unbox(v_a_786_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = l_Lean_trace_profiler;
v___x_966_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v_options_726_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; uint8_t v_foApprox_968_; uint8_t v_ctxApprox_969_; uint8_t v_quasiPatternApprox_970_; uint8_t v_constApprox_971_; uint8_t v_isDefEqStuckEx_972_; uint8_t v_unificationHints_973_; uint8_t v_proofIrrelevance_974_; uint8_t v_assignSyntheticOpaque_975_; uint8_t v_offsetCnstrs_976_; uint8_t v_etaStruct_977_; uint8_t v_univApprox_978_; uint8_t v_iota_979_; uint8_t v_beta_980_; uint8_t v_proj_981_; uint8_t v_zeta_982_; uint8_t v_zetaDelta_983_; uint8_t v_zetaUnused_984_; uint8_t v_zetaHave_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1023_; 
lean_del_object(v___x_788_);
lean_dec(v_a_786_);
lean_dec_ref(v___f_720_);
lean_dec_ref(v___x_719_);
lean_dec(v___x_717_);
v___x_967_ = l_Lean_Meta_Context_config(v___y_721_);
v_foApprox_968_ = lean_ctor_get_uint8(v___x_967_, 0);
v_ctxApprox_969_ = lean_ctor_get_uint8(v___x_967_, 1);
v_quasiPatternApprox_970_ = lean_ctor_get_uint8(v___x_967_, 2);
v_constApprox_971_ = lean_ctor_get_uint8(v___x_967_, 3);
v_isDefEqStuckEx_972_ = lean_ctor_get_uint8(v___x_967_, 4);
v_unificationHints_973_ = lean_ctor_get_uint8(v___x_967_, 5);
v_proofIrrelevance_974_ = lean_ctor_get_uint8(v___x_967_, 6);
v_assignSyntheticOpaque_975_ = lean_ctor_get_uint8(v___x_967_, 7);
v_offsetCnstrs_976_ = lean_ctor_get_uint8(v___x_967_, 8);
v_etaStruct_977_ = lean_ctor_get_uint8(v___x_967_, 10);
v_univApprox_978_ = lean_ctor_get_uint8(v___x_967_, 11);
v_iota_979_ = lean_ctor_get_uint8(v___x_967_, 12);
v_beta_980_ = lean_ctor_get_uint8(v___x_967_, 13);
v_proj_981_ = lean_ctor_get_uint8(v___x_967_, 14);
v_zeta_982_ = lean_ctor_get_uint8(v___x_967_, 15);
v_zetaDelta_983_ = lean_ctor_get_uint8(v___x_967_, 16);
v_zetaUnused_984_ = lean_ctor_get_uint8(v___x_967_, 17);
v_zetaHave_985_ = lean_ctor_get_uint8(v___x_967_, 18);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_987_ = v___x_967_;
v_isShared_988_ = v_isSharedCheck_1023_;
goto v_resetjp_986_;
}
else
{
lean_dec(v___x_967_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1023_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
uint8_t v_trackZetaDelta_989_; lean_object* v_zetaDeltaSet_990_; lean_object* v_lctx_991_; lean_object* v_localInstances_992_; lean_object* v_defEqCtx_x3f_993_; lean_object* v_synthPendingDepth_994_; lean_object* v_canUnfold_x3f_995_; uint8_t v_univApprox_996_; uint8_t v_inTypeClassResolution_997_; uint8_t v_cacheInferType_998_; lean_object* v_config_1000_; 
v_trackZetaDelta_989_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7);
v_zetaDeltaSet_990_ = lean_ctor_get(v___y_721_, 1);
v_lctx_991_ = lean_ctor_get(v___y_721_, 2);
v_localInstances_992_ = lean_ctor_get(v___y_721_, 3);
v_defEqCtx_x3f_993_ = lean_ctor_get(v___y_721_, 4);
v_synthPendingDepth_994_ = lean_ctor_get(v___y_721_, 5);
v_canUnfold_x3f_995_ = lean_ctor_get(v___y_721_, 6);
v_univApprox_996_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_997_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7 + 2);
v_cacheInferType_998_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7 + 3);
if (v_isShared_988_ == 0)
{
v_config_1000_ = v___x_987_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 0, v_foApprox_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 1, v_ctxApprox_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 2, v_quasiPatternApprox_970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 3, v_constApprox_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 4, v_isDefEqStuckEx_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 5, v_unificationHints_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 6, v_proofIrrelevance_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 7, v_assignSyntheticOpaque_975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 8, v_offsetCnstrs_976_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 10, v_etaStruct_977_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 11, v_univApprox_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 12, v_iota_979_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 13, v_beta_980_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 14, v_proj_981_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 15, v_zeta_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 16, v_zetaDelta_983_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 17, v_zetaUnused_984_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, 18, v_zetaHave_985_);
v_config_1000_ = v_reuseFailAlloc_1022_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
uint64_t v___x_1001_; uint64_t v___x_1002_; uint64_t v___x_1003_; uint64_t v___x_1004_; uint64_t v___x_1005_; uint64_t v_key_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_ctor_set_uint8(v_config_1000_, 9, v_transparency_712_);
v___x_1001_ = l_Lean_Meta_Context_configKey(v___y_721_);
v___x_1002_ = 2ULL;
v___x_1003_ = lean_uint64_shift_right(v___x_1001_, v___x_1002_);
v___x_1004_ = lean_uint64_shift_left(v___x_1003_, v___x_1002_);
v___x_1005_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_712_);
v_key_1006_ = lean_uint64_lor(v___x_1004_, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1007_, 0, v_config_1000_);
lean_ctor_set_uint64(v___x_1007_, sizeof(void*)*1, v_key_1006_);
lean_inc(v_canUnfold_x3f_995_);
lean_inc(v_synthPendingDepth_994_);
lean_inc(v_defEqCtx_x3f_993_);
lean_inc_ref(v_localInstances_992_);
lean_inc_ref(v_lctx_991_);
lean_inc(v_zetaDeltaSet_990_);
v___x_1008_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_zetaDeltaSet_990_);
lean_ctor_set(v___x_1008_, 2, v_lctx_991_);
lean_ctor_set(v___x_1008_, 3, v_localInstances_992_);
lean_ctor_set(v___x_1008_, 4, v_defEqCtx_x3f_993_);
lean_ctor_set(v___x_1008_, 5, v_synthPendingDepth_994_);
lean_ctor_set(v___x_1008_, 6, v_canUnfold_x3f_995_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*7, v_trackZetaDelta_989_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*7 + 1, v_univApprox_996_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*7 + 2, v_inTypeClassResolution_997_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*7 + 3, v_cacheInferType_998_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
v___x_1009_ = l_Lean_MVarId_apply(v_g_713_, v_e_714_, v_cfg_715_, v___x_716_, v___x_1008_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref(v___x_1009_);
v___x_1011_ = lean_box(0);
v___x_1012_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_966_, v_hasTrace_727_, v_a_1010_, v___x_1011_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1021_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1017_ = l_List_reverse___redArg(v_a_1013_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1017_);
v___x_1019_ = v___x_1015_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
return v___x_1012_;
}
}
else
{
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v___x_1009_;
}
}
}
}
else
{
lean_inc_ref(v_options_726_);
goto v___jp_857_;
}
}
else
{
lean_inc_ref(v_options_726_);
goto v___jp_857_;
}
v___jp_790_:
{
lean_object* v___x_794_; double v___x_795_; double v___x_796_; double v___x_797_; double v___x_798_; double v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; 
v___x_794_ = lean_io_mono_nanos_now();
v___x_795_ = lean_float_of_nat(v___y_792_);
v___x_796_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0);
v___x_797_ = lean_float_div(v___x_795_, v___x_796_);
v___x_798_ = lean_float_of_nat(v___x_794_);
v___x_799_ = lean_float_div(v___x_798_, v___x_796_);
v___x_800_ = lean_box_float(v___x_797_);
v___x_801_ = lean_box_float(v___x_799_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_a_793_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_unbox(v_a_786_);
lean_dec(v_a_786_);
v___x_805_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_717_, v___x_718_, v___x_719_, v_options_726_, v___x_804_, v___y_791_, v___f_720_, v___x_803_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec_ref(v_options_726_);
return v___x_805_;
}
v___jp_806_:
{
lean_object* v___x_811_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set_tag(v___x_788_, 1);
lean_ctor_set(v___x_788_, 0, v_a_809_);
v___x_811_ = v___x_788_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
v___y_791_ = v___y_807_;
v___y_792_ = v___y_808_;
v_a_793_ = v___x_811_;
goto v___jp_790_;
}
}
v___jp_813_:
{
if (lean_obj_tag(v___y_816_) == 0)
{
lean_object* v_a_817_; 
v_a_817_ = lean_ctor_get(v___y_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v___y_816_);
v___y_807_ = v___y_814_;
v___y_808_ = v___y_815_;
v_a_809_ = v_a_817_;
goto v___jp_806_;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_del_object(v___x_788_);
v_a_818_ = lean_ctor_get(v___y_816_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___y_816_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___y_816_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___y_816_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 0);
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
v___y_791_ = v___y_814_;
v___y_792_ = v___y_815_;
v_a_793_ = v___x_823_;
goto v___jp_790_;
}
}
}
}
v___jp_826_:
{
lean_object* v___x_830_; double v___x_831_; double v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; 
v___x_830_ = lean_io_get_num_heartbeats();
v___x_831_ = lean_float_of_nat(v___y_828_);
v___x_832_ = lean_float_of_nat(v___x_830_);
v___x_833_ = lean_box_float(v___x_831_);
v___x_834_ = lean_box_float(v___x_832_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v_a_829_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_unbox(v_a_786_);
lean_dec(v_a_786_);
v___x_838_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_717_, v___x_718_, v___x_719_, v_options_726_, v___x_837_, v___y_827_, v___f_720_, v___x_836_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec_ref(v_options_726_);
return v___x_838_;
}
v___jp_839_:
{
lean_object* v___x_843_; 
v___x_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_843_, 0, v_a_842_);
v___y_827_ = v___y_840_;
v___y_828_ = v___y_841_;
v_a_829_ = v___x_843_;
goto v___jp_826_;
}
v___jp_844_:
{
if (lean_obj_tag(v___y_847_) == 0)
{
lean_object* v_a_848_; 
v_a_848_ = lean_ctor_get(v___y_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref(v___y_847_);
v___y_840_ = v___y_845_;
v___y_841_ = v___y_846_;
v_a_842_ = v_a_848_;
goto v___jp_839_;
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v_a_849_ = lean_ctor_get(v___y_847_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___y_847_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___y_847_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___y_847_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 0);
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
v___y_827_ = v___y_845_;
v___y_828_ = v___y_846_;
v_a_829_ = v___x_854_;
goto v___jp_826_;
}
}
}
}
v___jp_857_:
{
lean_object* v___x_858_; lean_object* v_a_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_858_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg(v___y_724_);
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
v___x_860_ = l_Lean_trace_profiler_useHeartbeats;
v___x_861_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v_options_726_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v_foApprox_864_; uint8_t v_ctxApprox_865_; uint8_t v_quasiPatternApprox_866_; uint8_t v_constApprox_867_; uint8_t v_isDefEqStuckEx_868_; uint8_t v_unificationHints_869_; uint8_t v_proofIrrelevance_870_; uint8_t v_assignSyntheticOpaque_871_; uint8_t v_offsetCnstrs_872_; uint8_t v_etaStruct_873_; uint8_t v_univApprox_874_; uint8_t v_iota_875_; uint8_t v_beta_876_; uint8_t v_proj_877_; uint8_t v_zeta_878_; uint8_t v_zetaDelta_879_; uint8_t v_zetaUnused_880_; uint8_t v_zetaHave_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_912_; 
v___x_862_ = lean_io_mono_nanos_now();
v___x_863_ = l_Lean_Meta_Context_config(v___y_721_);
v_foApprox_864_ = lean_ctor_get_uint8(v___x_863_, 0);
v_ctxApprox_865_ = lean_ctor_get_uint8(v___x_863_, 1);
v_quasiPatternApprox_866_ = lean_ctor_get_uint8(v___x_863_, 2);
v_constApprox_867_ = lean_ctor_get_uint8(v___x_863_, 3);
v_isDefEqStuckEx_868_ = lean_ctor_get_uint8(v___x_863_, 4);
v_unificationHints_869_ = lean_ctor_get_uint8(v___x_863_, 5);
v_proofIrrelevance_870_ = lean_ctor_get_uint8(v___x_863_, 6);
v_assignSyntheticOpaque_871_ = lean_ctor_get_uint8(v___x_863_, 7);
v_offsetCnstrs_872_ = lean_ctor_get_uint8(v___x_863_, 8);
v_etaStruct_873_ = lean_ctor_get_uint8(v___x_863_, 10);
v_univApprox_874_ = lean_ctor_get_uint8(v___x_863_, 11);
v_iota_875_ = lean_ctor_get_uint8(v___x_863_, 12);
v_beta_876_ = lean_ctor_get_uint8(v___x_863_, 13);
v_proj_877_ = lean_ctor_get_uint8(v___x_863_, 14);
v_zeta_878_ = lean_ctor_get_uint8(v___x_863_, 15);
v_zetaDelta_879_ = lean_ctor_get_uint8(v___x_863_, 16);
v_zetaUnused_880_ = lean_ctor_get_uint8(v___x_863_, 17);
v_zetaHave_881_ = lean_ctor_get_uint8(v___x_863_, 18);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_912_ == 0)
{
v___x_883_ = v___x_863_;
v_isShared_884_ = v_isSharedCheck_912_;
goto v_resetjp_882_;
}
else
{
lean_dec(v___x_863_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_912_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
uint8_t v_trackZetaDelta_885_; lean_object* v_zetaDeltaSet_886_; lean_object* v_lctx_887_; lean_object* v_localInstances_888_; lean_object* v_defEqCtx_x3f_889_; lean_object* v_synthPendingDepth_890_; lean_object* v_canUnfold_x3f_891_; uint8_t v_univApprox_892_; uint8_t v_inTypeClassResolution_893_; uint8_t v_cacheInferType_894_; lean_object* v_config_896_; 
v_trackZetaDelta_885_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7);
v_zetaDeltaSet_886_ = lean_ctor_get(v___y_721_, 1);
v_lctx_887_ = lean_ctor_get(v___y_721_, 2);
v_localInstances_888_ = lean_ctor_get(v___y_721_, 3);
v_defEqCtx_x3f_889_ = lean_ctor_get(v___y_721_, 4);
v_synthPendingDepth_890_ = lean_ctor_get(v___y_721_, 5);
v_canUnfold_x3f_891_ = lean_ctor_get(v___y_721_, 6);
v_univApprox_892_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_893_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7 + 2);
v_cacheInferType_894_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7 + 3);
if (v_isShared_884_ == 0)
{
v_config_896_ = v___x_883_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 0, v_foApprox_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 1, v_ctxApprox_865_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 2, v_quasiPatternApprox_866_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 3, v_constApprox_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 4, v_isDefEqStuckEx_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 5, v_unificationHints_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 6, v_proofIrrelevance_870_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 7, v_assignSyntheticOpaque_871_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 8, v_offsetCnstrs_872_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 10, v_etaStruct_873_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 11, v_univApprox_874_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 12, v_iota_875_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 13, v_beta_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 14, v_proj_877_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 15, v_zeta_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 16, v_zetaDelta_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 17, v_zetaUnused_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, 18, v_zetaHave_881_);
v_config_896_ = v_reuseFailAlloc_911_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
uint64_t v___x_897_; uint64_t v___x_898_; uint64_t v___x_899_; uint64_t v___x_900_; uint64_t v___x_901_; uint64_t v_key_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
lean_ctor_set_uint8(v_config_896_, 9, v_transparency_712_);
v___x_897_ = l_Lean_Meta_Context_configKey(v___y_721_);
v___x_898_ = 2ULL;
v___x_899_ = lean_uint64_shift_right(v___x_897_, v___x_898_);
v___x_900_ = lean_uint64_shift_left(v___x_899_, v___x_898_);
v___x_901_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_712_);
v_key_902_ = lean_uint64_lor(v___x_900_, v___x_901_);
v___x_903_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_903_, 0, v_config_896_);
lean_ctor_set_uint64(v___x_903_, sizeof(void*)*1, v_key_902_);
lean_inc(v_canUnfold_x3f_891_);
lean_inc(v_synthPendingDepth_890_);
lean_inc(v_defEqCtx_x3f_889_);
lean_inc_ref(v_localInstances_888_);
lean_inc_ref(v_lctx_887_);
lean_inc(v_zetaDeltaSet_886_);
v___x_904_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v_zetaDeltaSet_886_);
lean_ctor_set(v___x_904_, 2, v_lctx_887_);
lean_ctor_set(v___x_904_, 3, v_localInstances_888_);
lean_ctor_set(v___x_904_, 4, v_defEqCtx_x3f_889_);
lean_ctor_set(v___x_904_, 5, v_synthPendingDepth_890_);
lean_ctor_set(v___x_904_, 6, v_canUnfold_x3f_891_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*7, v_trackZetaDelta_885_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*7 + 1, v_univApprox_892_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*7 + 2, v_inTypeClassResolution_893_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*7 + 3, v_cacheInferType_894_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
v___x_905_ = l_Lean_MVarId_apply(v_g_713_, v_e_714_, v_cfg_715_, v___x_716_, v___x_904_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
lean_dec_ref(v___x_905_);
v___x_907_ = lean_box(0);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
v___x_908_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_861_, v_hasTrace_727_, v_a_906_, v___x_907_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_910_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref(v___x_908_);
v___x_910_ = l_List_reverse___redArg(v_a_909_);
v___y_807_ = v_a_859_;
v___y_808_ = v___x_862_;
v_a_809_ = v___x_910_;
goto v___jp_806_;
}
else
{
v___y_814_ = v_a_859_;
v___y_815_ = v___x_862_;
v___y_816_ = v___x_908_;
goto v___jp_813_;
}
}
else
{
v___y_814_ = v_a_859_;
v___y_815_ = v___x_862_;
v___y_816_ = v___x_905_;
goto v___jp_813_;
}
}
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v_foApprox_915_; uint8_t v_ctxApprox_916_; uint8_t v_quasiPatternApprox_917_; uint8_t v_constApprox_918_; uint8_t v_isDefEqStuckEx_919_; uint8_t v_unificationHints_920_; uint8_t v_proofIrrelevance_921_; uint8_t v_assignSyntheticOpaque_922_; uint8_t v_offsetCnstrs_923_; uint8_t v_etaStruct_924_; uint8_t v_univApprox_925_; uint8_t v_iota_926_; uint8_t v_beta_927_; uint8_t v_proj_928_; uint8_t v_zeta_929_; uint8_t v_zetaDelta_930_; uint8_t v_zetaUnused_931_; uint8_t v_zetaHave_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_963_; 
lean_del_object(v___x_788_);
v___x_913_ = lean_io_get_num_heartbeats();
v___x_914_ = l_Lean_Meta_Context_config(v___y_721_);
v_foApprox_915_ = lean_ctor_get_uint8(v___x_914_, 0);
v_ctxApprox_916_ = lean_ctor_get_uint8(v___x_914_, 1);
v_quasiPatternApprox_917_ = lean_ctor_get_uint8(v___x_914_, 2);
v_constApprox_918_ = lean_ctor_get_uint8(v___x_914_, 3);
v_isDefEqStuckEx_919_ = lean_ctor_get_uint8(v___x_914_, 4);
v_unificationHints_920_ = lean_ctor_get_uint8(v___x_914_, 5);
v_proofIrrelevance_921_ = lean_ctor_get_uint8(v___x_914_, 6);
v_assignSyntheticOpaque_922_ = lean_ctor_get_uint8(v___x_914_, 7);
v_offsetCnstrs_923_ = lean_ctor_get_uint8(v___x_914_, 8);
v_etaStruct_924_ = lean_ctor_get_uint8(v___x_914_, 10);
v_univApprox_925_ = lean_ctor_get_uint8(v___x_914_, 11);
v_iota_926_ = lean_ctor_get_uint8(v___x_914_, 12);
v_beta_927_ = lean_ctor_get_uint8(v___x_914_, 13);
v_proj_928_ = lean_ctor_get_uint8(v___x_914_, 14);
v_zeta_929_ = lean_ctor_get_uint8(v___x_914_, 15);
v_zetaDelta_930_ = lean_ctor_get_uint8(v___x_914_, 16);
v_zetaUnused_931_ = lean_ctor_get_uint8(v___x_914_, 17);
v_zetaHave_932_ = lean_ctor_get_uint8(v___x_914_, 18);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_963_ == 0)
{
v___x_934_ = v___x_914_;
v_isShared_935_ = v_isSharedCheck_963_;
goto v_resetjp_933_;
}
else
{
lean_dec(v___x_914_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_963_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
uint8_t v_trackZetaDelta_936_; lean_object* v_zetaDeltaSet_937_; lean_object* v_lctx_938_; lean_object* v_localInstances_939_; lean_object* v_defEqCtx_x3f_940_; lean_object* v_synthPendingDepth_941_; lean_object* v_canUnfold_x3f_942_; uint8_t v_univApprox_943_; uint8_t v_inTypeClassResolution_944_; uint8_t v_cacheInferType_945_; lean_object* v_config_947_; 
v_trackZetaDelta_936_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7);
v_zetaDeltaSet_937_ = lean_ctor_get(v___y_721_, 1);
v_lctx_938_ = lean_ctor_get(v___y_721_, 2);
v_localInstances_939_ = lean_ctor_get(v___y_721_, 3);
v_defEqCtx_x3f_940_ = lean_ctor_get(v___y_721_, 4);
v_synthPendingDepth_941_ = lean_ctor_get(v___y_721_, 5);
v_canUnfold_x3f_942_ = lean_ctor_get(v___y_721_, 6);
v_univApprox_943_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_944_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7 + 2);
v_cacheInferType_945_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*7 + 3);
if (v_isShared_935_ == 0)
{
v_config_947_ = v___x_934_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 0, v_foApprox_915_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 1, v_ctxApprox_916_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 2, v_quasiPatternApprox_917_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 3, v_constApprox_918_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 4, v_isDefEqStuckEx_919_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 5, v_unificationHints_920_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 6, v_proofIrrelevance_921_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 7, v_assignSyntheticOpaque_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 8, v_offsetCnstrs_923_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 10, v_etaStruct_924_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 11, v_univApprox_925_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 12, v_iota_926_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 13, v_beta_927_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 14, v_proj_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 15, v_zeta_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 16, v_zetaDelta_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 17, v_zetaUnused_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, 18, v_zetaHave_932_);
v_config_947_ = v_reuseFailAlloc_962_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
uint64_t v___x_948_; uint64_t v___x_949_; uint64_t v___x_950_; uint64_t v___x_951_; uint64_t v___x_952_; uint64_t v_key_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
lean_ctor_set_uint8(v_config_947_, 9, v_transparency_712_);
v___x_948_ = l_Lean_Meta_Context_configKey(v___y_721_);
v___x_949_ = 2ULL;
v___x_950_ = lean_uint64_shift_right(v___x_948_, v___x_949_);
v___x_951_ = lean_uint64_shift_left(v___x_950_, v___x_949_);
v___x_952_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_712_);
v_key_953_ = lean_uint64_lor(v___x_951_, v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_954_, 0, v_config_947_);
lean_ctor_set_uint64(v___x_954_, sizeof(void*)*1, v_key_953_);
lean_inc(v_canUnfold_x3f_942_);
lean_inc(v_synthPendingDepth_941_);
lean_inc(v_defEqCtx_x3f_940_);
lean_inc_ref(v_localInstances_939_);
lean_inc_ref(v_lctx_938_);
lean_inc(v_zetaDeltaSet_937_);
v___x_955_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v_zetaDeltaSet_937_);
lean_ctor_set(v___x_955_, 2, v_lctx_938_);
lean_ctor_set(v___x_955_, 3, v_localInstances_939_);
lean_ctor_set(v___x_955_, 4, v_defEqCtx_x3f_940_);
lean_ctor_set(v___x_955_, 5, v_synthPendingDepth_941_);
lean_ctor_set(v___x_955_, 6, v_canUnfold_x3f_942_);
lean_ctor_set_uint8(v___x_955_, sizeof(void*)*7, v_trackZetaDelta_936_);
lean_ctor_set_uint8(v___x_955_, sizeof(void*)*7 + 1, v_univApprox_943_);
lean_ctor_set_uint8(v___x_955_, sizeof(void*)*7 + 2, v_inTypeClassResolution_944_);
lean_ctor_set_uint8(v___x_955_, sizeof(void*)*7 + 3, v_cacheInferType_945_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
v___x_956_ = l_Lean_MVarId_apply(v_g_713_, v_e_714_, v_cfg_715_, v___x_716_, v___x_955_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref(v___x_956_);
v___x_958_ = lean_box(0);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
v___x_959_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(v___x_861_, v_a_957_, v___x_958_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_961_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref(v___x_959_);
v___x_961_ = l_List_reverse___redArg(v_a_960_);
v___y_840_ = v_a_859_;
v___y_841_ = v___x_913_;
v_a_842_ = v___x_961_;
goto v___jp_839_;
}
else
{
v___y_845_ = v_a_859_;
v___y_846_ = v___x_913_;
v___y_847_ = v___x_959_;
goto v___jp_844_;
}
}
else
{
v___y_845_ = v_a_859_;
v___y_846_ = v___x_913_;
v___y_847_ = v___x_956_;
goto v___jp_844_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_1025_, lean_object* v_g_1026_, lean_object* v_e_1027_, lean_object* v_cfg_1028_, lean_object* v___x_1029_, lean_object* v___x_1030_, lean_object* v___x_1031_, lean_object* v___x_1032_, lean_object* v___f_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
uint8_t v_transparency_boxed_1039_; uint8_t v___x_14451__boxed_1040_; lean_object* v_res_1041_; 
v_transparency_boxed_1039_ = lean_unbox(v_transparency_1025_);
v___x_14451__boxed_1040_ = lean_unbox(v___x_1031_);
v_res_1041_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_1039_, v_g_1026_, v_e_1027_, v_cfg_1028_, v___x_1029_, v___x_1030_, v___x_14451__boxed_1040_, v___x_1032_, v___f_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_1043_, lean_object* v_g_1044_, lean_object* v_cfg_1045_, lean_object* v_e_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___f_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; 
lean_inc_ref(v_e_1046_);
v___f_1052_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1052_, 0, v_e_1046_);
v___x_1053_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_1054_ = lean_box(0);
v___x_1055_ = 1;
v___x_1056_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_1057_ = lean_box(v_transparency_1043_);
v___x_1058_ = lean_box(v___x_1055_);
v___f_1059_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_1059_, 0, v___x_1057_);
lean_closure_set(v___f_1059_, 1, v_g_1044_);
lean_closure_set(v___f_1059_, 2, v_e_1046_);
lean_closure_set(v___f_1059_, 3, v_cfg_1045_);
lean_closure_set(v___f_1059_, 4, v___x_1054_);
lean_closure_set(v___f_1059_, 5, v___x_1053_);
lean_closure_set(v___f_1059_, 6, v___x_1058_);
lean_closure_set(v___f_1059_, 7, v___x_1056_);
lean_closure_set(v___f_1059_, 8, v___f_1052_);
v___x_1060_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7___redArg(v___f_1059_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_1061_, lean_object* v_g_1062_, lean_object* v_cfg_1063_, lean_object* v_e_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v_transparency_boxed_1070_; lean_object* v_res_1071_; 
v_transparency_boxed_1070_ = lean_unbox(v_transparency_1061_);
v_res_1071_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_1070_, v_g_1062_, v_cfg_1063_, v_e_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_1072_, uint8_t v_transparency_1073_, lean_object* v_lemmas_1074_, lean_object* v_g_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_1074_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1090_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1090_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1090_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1084_ = lean_box(v_transparency_1073_);
v___f_1085_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1085_, 0, v___x_1084_);
lean_closure_set(v___f_1085_, 1, v_g_1075_);
lean_closure_set(v___f_1085_, 2, v_cfg_1072_);
v___x_1086_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_1086_, 0, lean_box(0));
lean_closure_set(v___x_1086_, 1, lean_box(0));
lean_closure_set(v___x_1086_, 2, v___f_1085_);
lean_closure_set(v___x_1086_, 3, v_a_1080_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1086_);
v___x_1088_ = v___x_1082_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_g_1075_);
lean_dec_ref(v_cfg_1072_);
v_a_1091_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1079_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1079_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_1099_, lean_object* v_transparency_1100_, lean_object* v_lemmas_1101_, lean_object* v_g_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
uint8_t v_transparency_boxed_1106_; lean_object* v_res_1107_; 
v_transparency_boxed_1106_ = lean_unbox(v_transparency_1100_);
v_res_1107_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1099_, v_transparency_boxed_1106_, v_lemmas_1101_, v_g_1102_, v_a_1103_, v_a_1104_);
lean_dec(v_a_1104_);
lean_dec(v_a_1103_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_1108_, uint8_t v_transparency_1109_, lean_object* v_lemmas_1110_, lean_object* v_g_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1108_, v_transparency_1109_, v_lemmas_1110_, v_g_1111_, v_a_1113_, v_a_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_1118_, lean_object* v_transparency_1119_, lean_object* v_lemmas_1120_, lean_object* v_g_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
uint8_t v_transparency_boxed_1127_; lean_object* v_res_1128_; 
v_transparency_boxed_1127_ = lean_unbox(v_transparency_1119_);
v_res_1128_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_1118_, v_transparency_boxed_1127_, v_lemmas_1120_, v_g_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6(lean_object* v_00_u03b1_1129_, lean_object* v_x_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___redArg(v_x_1130_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1137_, lean_object* v_x_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6(v_00_u03b1_1137_, v_x_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1145_, uint8_t v_transparency_1146_, lean_object* v_lemmas_1147_, lean_object* v_g_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1145_, v_transparency_1146_, v_lemmas_1147_, v_g_1148_, v_a_1150_, v_a_1152_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1156_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref(v___x_1154_);
v___x_1156_ = l_Lean_Meta_Iterator_head___redArg(v_a_1155_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
return v___x_1156_;
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
v_a_1157_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1154_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1154_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1165_, lean_object* v_transparency_1166_, lean_object* v_lemmas_1167_, lean_object* v_g_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
uint8_t v_transparency_boxed_1174_; lean_object* v_res_1175_; 
v_transparency_boxed_1174_ = lean_unbox(v_transparency_1166_);
v_res_1175_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1165_, v_transparency_boxed_1174_, v_lemmas_1167_, v_g_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1176_){
_start:
{
lean_object* v_toApplyRulesConfig_1177_; lean_object* v_toBacktrackConfig_1178_; 
v_toApplyRulesConfig_1177_ = lean_ctor_get(v_x_1176_, 0);
v_toBacktrackConfig_1178_ = lean_ctor_get(v_toApplyRulesConfig_1177_, 0);
lean_inc_ref(v_toBacktrackConfig_1178_);
return v_toBacktrackConfig_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1179_);
lean_dec_ref(v_x_1179_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1183_, lean_object* v_discharge_1184_, lean_object* v_g_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
lean_inc(v___y_1189_);
lean_inc_ref(v___y_1188_);
lean_inc(v___y_1187_);
lean_inc_ref(v___y_1186_);
lean_inc(v_g_1185_);
v___x_1191_ = lean_apply_6(v_test_1183_, v_g_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, lean_box(0));
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1202_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
uint8_t v___x_1196_; 
v___x_1196_ = lean_unbox(v_a_1192_);
lean_dec(v_a_1192_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
lean_del_object(v___x_1194_);
v___x_1197_ = lean_apply_6(v_discharge_1184_, v_g_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, lean_box(0));
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v_g_1185_);
lean_dec_ref(v_discharge_1184_);
v___x_1198_ = lean_box(0);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1198_);
v___x_1200_ = v___x_1194_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v_g_1185_);
lean_dec_ref(v_discharge_1184_);
v_a_1203_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1191_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1191_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1211_, lean_object* v_discharge_1212_, lean_object* v_g_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1211_, v_discharge_1212_, v_g_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1220_, lean_object* v_test_1221_){
_start:
{
lean_object* v_toApplyRulesConfig_1222_; lean_object* v_toBacktrackConfig_1223_; uint8_t v_backtracking_1224_; uint8_t v_intro_1225_; uint8_t v_constructor_1226_; uint8_t v_suggestions_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1259_; 
v_toApplyRulesConfig_1222_ = lean_ctor_get(v_cfg_1220_, 0);
lean_inc_ref(v_toApplyRulesConfig_1222_);
v_toBacktrackConfig_1223_ = lean_ctor_get(v_toApplyRulesConfig_1222_, 0);
lean_inc_ref(v_toBacktrackConfig_1223_);
v_backtracking_1224_ = lean_ctor_get_uint8(v_cfg_1220_, sizeof(void*)*1);
v_intro_1225_ = lean_ctor_get_uint8(v_cfg_1220_, sizeof(void*)*1 + 1);
v_constructor_1226_ = lean_ctor_get_uint8(v_cfg_1220_, sizeof(void*)*1 + 2);
v_suggestions_1227_ = lean_ctor_get_uint8(v_cfg_1220_, sizeof(void*)*1 + 3);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_cfg_1220_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v_cfg_1220_, 0);
lean_dec(v_unused_1260_);
v___x_1229_ = v_cfg_1220_;
v_isShared_1230_ = v_isSharedCheck_1259_;
goto v_resetjp_1228_;
}
else
{
lean_dec(v_cfg_1220_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1259_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v_toApplyConfig_1231_; uint8_t v_transparency_1232_; uint8_t v_symm_1233_; uint8_t v_exfalso_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1257_; 
v_toApplyConfig_1231_ = lean_ctor_get(v_toApplyRulesConfig_1222_, 1);
v_transparency_1232_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1222_, sizeof(void*)*2);
v_symm_1233_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1222_, sizeof(void*)*2 + 1);
v_exfalso_1234_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1222_, sizeof(void*)*2 + 2);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_toApplyRulesConfig_1222_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v_toApplyRulesConfig_1222_, 0);
lean_dec(v_unused_1258_);
v___x_1236_ = v_toApplyRulesConfig_1222_;
v_isShared_1237_ = v_isSharedCheck_1257_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_toApplyConfig_1231_);
lean_dec(v_toApplyRulesConfig_1222_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1257_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v_maxDepth_1238_; lean_object* v_proc_1239_; lean_object* v_suspend_1240_; lean_object* v_discharge_1241_; uint8_t v_commitIndependentGoals_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1256_; 
v_maxDepth_1238_ = lean_ctor_get(v_toBacktrackConfig_1223_, 0);
v_proc_1239_ = lean_ctor_get(v_toBacktrackConfig_1223_, 1);
v_suspend_1240_ = lean_ctor_get(v_toBacktrackConfig_1223_, 2);
v_discharge_1241_ = lean_ctor_get(v_toBacktrackConfig_1223_, 3);
v_commitIndependentGoals_1242_ = lean_ctor_get_uint8(v_toBacktrackConfig_1223_, sizeof(void*)*4);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_toBacktrackConfig_1223_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1244_ = v_toBacktrackConfig_1223_;
v_isShared_1245_ = v_isSharedCheck_1256_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_discharge_1241_);
lean_inc(v_suspend_1240_);
lean_inc(v_proc_1239_);
lean_inc(v_maxDepth_1238_);
lean_dec(v_toBacktrackConfig_1223_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1256_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___f_1246_; lean_object* v___x_1248_; 
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1246_, 0, v_test_1221_);
lean_closure_set(v___f_1246_, 1, v_discharge_1241_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 3, v___f_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_maxDepth_1238_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_proc_1239_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_suspend_1240_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v___f_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1255_, sizeof(void*)*4, v_commitIndependentGoals_1242_);
v___x_1248_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1250_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1248_);
v___x_1250_ = v___x_1236_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_toApplyConfig_1231_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, sizeof(void*)*2, v_transparency_1232_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, sizeof(void*)*2 + 1, v_symm_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, sizeof(void*)*2 + 2, v_exfalso_1234_);
v___x_1250_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1252_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1250_);
v___x_1252_ = v___x_1229_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1253_, sizeof(void*)*1, v_backtracking_1224_);
lean_ctor_set_uint8(v_reuseFailAlloc_1253_, sizeof(void*)*1 + 1, v_intro_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1253_, sizeof(void*)*1 + 2, v_constructor_1226_);
lean_ctor_set_uint8(v_reuseFailAlloc_1253_, sizeof(void*)*1 + 3, v_suggestions_1227_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1261_, lean_object* v_proc_1262_, lean_object* v_orig_1263_, lean_object* v_goals_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
if (lean_obj_tag(v_goals_1264_) == 0)
{
lean_object* v___x_1270_; 
lean_dec_ref(v_proc_1262_);
v___x_1270_ = lean_apply_7(v_proc_1261_, v_orig_1263_, v_goals_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, lean_box(0));
return v___x_1270_;
}
else
{
lean_object* v_head_1271_; lean_object* v_tail_1272_; lean_object* v___x_1273_; 
v_head_1271_ = lean_ctor_get(v_goals_1264_, 0);
v_tail_1272_ = lean_ctor_get(v_goals_1264_, 1);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
lean_inc(v_head_1271_);
v___x_1273_ = lean_apply_6(v_proc_1262_, v_head_1271_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, lean_box(0));
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1283_; 
lean_inc(v_tail_1272_);
lean_dec_ref(v_goals_1264_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v_orig_1263_);
lean_dec_ref(v_proc_1261_);
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1283_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1283_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1278_ = l_List_appendTR___redArg(v_a_1274_, v_tail_1272_);
v___x_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1279_);
v___x_1281_ = v___x_1276_;
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
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1296_; 
v_a_1284_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1286_ = v___x_1273_;
v_isShared_1287_ = v_isSharedCheck_1296_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1273_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1296_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
uint8_t v___y_1289_; uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_Exception_isInterrupt(v_a_1284_);
if (v___x_1294_ == 0)
{
uint8_t v___x_1295_; 
lean_inc(v_a_1284_);
v___x_1295_ = l_Lean_Exception_isRuntime(v_a_1284_);
v___y_1289_ = v___x_1295_;
goto v___jp_1288_;
}
else
{
v___y_1289_ = v___x_1294_;
goto v___jp_1288_;
}
v___jp_1288_:
{
if (v___y_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_del_object(v___x_1286_);
lean_dec(v_a_1284_);
v___x_1290_ = lean_apply_7(v_proc_1261_, v_orig_1263_, v_goals_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, lean_box(0));
return v___x_1290_;
}
else
{
lean_object* v___x_1292_; 
lean_dec_ref(v_goals_1264_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v_orig_1263_);
lean_dec_ref(v_proc_1261_);
if (v_isShared_1287_ == 0)
{
v___x_1292_ = v___x_1286_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1284_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1297_, lean_object* v_proc_1298_, lean_object* v_orig_1299_, lean_object* v_goals_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1297_, v_proc_1298_, v_orig_1299_, v_goals_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1307_, lean_object* v_proc_1308_){
_start:
{
lean_object* v_toApplyRulesConfig_1309_; lean_object* v_toBacktrackConfig_1310_; uint8_t v_backtracking_1311_; uint8_t v_intro_1312_; uint8_t v_constructor_1313_; uint8_t v_suggestions_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1346_; 
v_toApplyRulesConfig_1309_ = lean_ctor_get(v_cfg_1307_, 0);
lean_inc_ref(v_toApplyRulesConfig_1309_);
v_toBacktrackConfig_1310_ = lean_ctor_get(v_toApplyRulesConfig_1309_, 0);
lean_inc_ref(v_toBacktrackConfig_1310_);
v_backtracking_1311_ = lean_ctor_get_uint8(v_cfg_1307_, sizeof(void*)*1);
v_intro_1312_ = lean_ctor_get_uint8(v_cfg_1307_, sizeof(void*)*1 + 1);
v_constructor_1313_ = lean_ctor_get_uint8(v_cfg_1307_, sizeof(void*)*1 + 2);
v_suggestions_1314_ = lean_ctor_get_uint8(v_cfg_1307_, sizeof(void*)*1 + 3);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_cfg_1307_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v_cfg_1307_, 0);
lean_dec(v_unused_1347_);
v___x_1316_ = v_cfg_1307_;
v_isShared_1317_ = v_isSharedCheck_1346_;
goto v_resetjp_1315_;
}
else
{
lean_dec(v_cfg_1307_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1346_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v_toApplyConfig_1318_; uint8_t v_transparency_1319_; uint8_t v_symm_1320_; uint8_t v_exfalso_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1344_; 
v_toApplyConfig_1318_ = lean_ctor_get(v_toApplyRulesConfig_1309_, 1);
v_transparency_1319_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1309_, sizeof(void*)*2);
v_symm_1320_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1309_, sizeof(void*)*2 + 1);
v_exfalso_1321_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1309_, sizeof(void*)*2 + 2);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_toApplyRulesConfig_1309_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v_toApplyRulesConfig_1309_, 0);
lean_dec(v_unused_1345_);
v___x_1323_ = v_toApplyRulesConfig_1309_;
v_isShared_1324_ = v_isSharedCheck_1344_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_toApplyConfig_1318_);
lean_dec(v_toApplyRulesConfig_1309_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1344_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_maxDepth_1325_; lean_object* v_proc_1326_; lean_object* v_suspend_1327_; lean_object* v_discharge_1328_; uint8_t v_commitIndependentGoals_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1343_; 
v_maxDepth_1325_ = lean_ctor_get(v_toBacktrackConfig_1310_, 0);
v_proc_1326_ = lean_ctor_get(v_toBacktrackConfig_1310_, 1);
v_suspend_1327_ = lean_ctor_get(v_toBacktrackConfig_1310_, 2);
v_discharge_1328_ = lean_ctor_get(v_toBacktrackConfig_1310_, 3);
v_commitIndependentGoals_1329_ = lean_ctor_get_uint8(v_toBacktrackConfig_1310_, sizeof(void*)*4);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_toBacktrackConfig_1310_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1331_ = v_toBacktrackConfig_1310_;
v_isShared_1332_ = v_isSharedCheck_1343_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_discharge_1328_);
lean_inc(v_suspend_1327_);
lean_inc(v_proc_1326_);
lean_inc(v_maxDepth_1325_);
lean_dec(v_toBacktrackConfig_1310_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1343_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___f_1333_; lean_object* v___x_1335_; 
v___f_1333_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1333_, 0, v_proc_1326_);
lean_closure_set(v___f_1333_, 1, v_proc_1308_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v___f_1333_);
v___x_1335_ = v___x_1331_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_maxDepth_1325_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___f_1333_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_suspend_1327_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_discharge_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*4, v_commitIndependentGoals_1329_);
v___x_1335_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1337_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1335_);
v___x_1337_ = v___x_1323_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_toApplyConfig_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*2, v_transparency_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*2 + 1, v_symm_1320_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*2 + 2, v_exfalso_1321_);
v___x_1337_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1339_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1337_);
v___x_1339_ = v___x_1316_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*1, v_backtracking_1311_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*1 + 1, v_intro_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*1 + 2, v_constructor_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*1 + 3, v_suggestions_1314_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = 1;
v___x_1355_ = l_Lean_Meta_intro1Core(v_g_1348_, v___x_1354_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1373_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1373_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1373_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v_snd_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1371_; 
v_snd_1360_ = lean_ctor_get(v_a_1356_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_1356_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v_a_1356_, 0);
lean_dec(v_unused_1372_);
v___x_1362_ = v_a_1356_;
v_isShared_1363_ = v_isSharedCheck_1371_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_snd_1360_);
lean_dec(v_a_1356_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1371_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = lean_box(0);
if (v_isShared_1363_ == 0)
{
lean_ctor_set_tag(v___x_1362_, 1);
lean_ctor_set(v___x_1362_, 1, v___x_1364_);
lean_ctor_set(v___x_1362_, 0, v_snd_1360_);
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_snd_1360_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1366_);
v___x_1368_ = v___x_1358_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_a_1374_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1355_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1355_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1390_){
_start:
{
lean_object* v___f_1391_; lean_object* v___x_1392_; 
v___f_1391_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1392_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1390_, v___f_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_){
_start:
{
lean_object* v_ks_1397_; lean_object* v_vs_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1422_; 
v_ks_1397_ = lean_ctor_get(v_x_1393_, 0);
v_vs_1398_ = lean_ctor_get(v_x_1393_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_x_1393_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1400_ = v_x_1393_;
v_isShared_1401_ = v_isSharedCheck_1422_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_vs_1398_);
lean_inc(v_ks_1397_);
lean_dec(v_x_1393_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1422_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = lean_array_get_size(v_ks_1397_);
v___x_1403_ = lean_nat_dec_lt(v_x_1394_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_dec(v_x_1394_);
v___x_1404_ = lean_array_push(v_ks_1397_, v_x_1395_);
v___x_1405_ = lean_array_push(v_vs_1398_, v_x_1396_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v___x_1405_);
lean_ctor_set(v___x_1400_, 0, v___x_1404_);
v___x_1407_ = v___x_1400_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
lean_object* v_k_x27_1409_; uint8_t v___x_1410_; 
v_k_x27_1409_ = lean_array_fget_borrowed(v_ks_1397_, v_x_1394_);
v___x_1410_ = l_Lean_instBEqMVarId_beq(v_x_1395_, v_k_x27_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1412_; 
if (v_isShared_1401_ == 0)
{
v___x_1412_ = v___x_1400_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_ks_1397_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_vs_1398_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_unsigned_to_nat(1u);
v___x_1414_ = lean_nat_add(v_x_1394_, v___x_1413_);
lean_dec(v_x_1394_);
v_x_1393_ = v___x_1412_;
v_x_1394_ = v___x_1414_;
goto _start;
}
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1417_ = lean_array_fset(v_ks_1397_, v_x_1394_, v_x_1395_);
v___x_1418_ = lean_array_fset(v_vs_1398_, v_x_1394_, v_x_1396_);
lean_dec(v_x_1394_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v___x_1418_);
lean_ctor_set(v___x_1400_, 0, v___x_1417_);
v___x_1420_ = v___x_1400_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1423_, lean_object* v_k_1424_, lean_object* v_v_1425_){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1423_, v___x_1426_, v_k_1424_, v_v_1425_);
return v___x_1427_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; 
v___x_1428_ = ((size_t)5ULL);
v___x_1429_ = ((size_t)1ULL);
v___x_1430_ = lean_usize_shift_left(v___x_1429_, v___x_1428_);
return v___x_1430_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1431_; size_t v___x_1432_; size_t v___x_1433_; 
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1433_ = lean_usize_sub(v___x_1432_, v___x_1431_);
return v___x_1433_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1435_, size_t v_x_1436_, size_t v_x_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_){
_start:
{
if (lean_obj_tag(v_x_1435_) == 0)
{
lean_object* v_es_1440_; size_t v___x_1441_; size_t v___x_1442_; size_t v___x_1443_; size_t v___x_1444_; lean_object* v_j_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v_es_1440_ = lean_ctor_get(v_x_1435_, 0);
v___x_1441_ = ((size_t)5ULL);
v___x_1442_ = ((size_t)1ULL);
v___x_1443_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1444_ = lean_usize_land(v_x_1436_, v___x_1443_);
v_j_1445_ = lean_usize_to_nat(v___x_1444_);
v___x_1446_ = lean_array_get_size(v_es_1440_);
v___x_1447_ = lean_nat_dec_lt(v_j_1445_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_dec(v_j_1445_);
lean_dec(v_x_1439_);
lean_dec(v_x_1438_);
return v_x_1435_;
}
else
{
lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1484_; 
lean_inc_ref(v_es_1440_);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_x_1435_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; 
v_unused_1485_ = lean_ctor_get(v_x_1435_, 0);
lean_dec(v_unused_1485_);
v___x_1449_ = v_x_1435_;
v_isShared_1450_ = v_isSharedCheck_1484_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v_x_1435_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1484_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v_v_1451_; lean_object* v___x_1452_; lean_object* v_xs_x27_1453_; lean_object* v___y_1455_; 
v_v_1451_ = lean_array_fget(v_es_1440_, v_j_1445_);
v___x_1452_ = lean_box(0);
v_xs_x27_1453_ = lean_array_fset(v_es_1440_, v_j_1445_, v___x_1452_);
switch(lean_obj_tag(v_v_1451_))
{
case 0:
{
lean_object* v_key_1460_; lean_object* v_val_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1471_; 
v_key_1460_ = lean_ctor_get(v_v_1451_, 0);
v_val_1461_ = lean_ctor_get(v_v_1451_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_v_1451_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1463_ = v_v_1451_;
v_isShared_1464_ = v_isSharedCheck_1471_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_val_1461_);
lean_inc(v_key_1460_);
lean_dec(v_v_1451_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1471_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
uint8_t v___x_1465_; 
v___x_1465_ = l_Lean_instBEqMVarId_beq(v_x_1438_, v_key_1460_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_del_object(v___x_1463_);
v___x_1466_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1460_, v_val_1461_, v_x_1438_, v_x_1439_);
v___x_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
v___y_1455_ = v___x_1467_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1469_; 
lean_dec(v_val_1461_);
lean_dec(v_key_1460_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 1, v_x_1439_);
lean_ctor_set(v___x_1463_, 0, v_x_1438_);
v___x_1469_ = v___x_1463_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_x_1438_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_x_1439_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
v___y_1455_ = v___x_1469_;
goto v___jp_1454_;
}
}
}
}
case 1:
{
lean_object* v_node_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1482_; 
v_node_1472_ = lean_ctor_get(v_v_1451_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_v_1451_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1474_ = v_v_1451_;
v_isShared_1475_ = v_isSharedCheck_1482_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_node_1472_);
lean_dec(v_v_1451_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1482_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
size_t v___x_1476_; size_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1476_ = lean_usize_shift_right(v_x_1436_, v___x_1441_);
v___x_1477_ = lean_usize_add(v_x_1437_, v___x_1442_);
v___x_1478_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1472_, v___x_1476_, v___x_1477_, v_x_1438_, v_x_1439_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v___x_1478_);
v___x_1480_ = v___x_1474_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
v___y_1455_ = v___x_1480_;
goto v___jp_1454_;
}
}
}
default: 
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_x_1438_);
lean_ctor_set(v___x_1483_, 1, v_x_1439_);
v___y_1455_ = v___x_1483_;
goto v___jp_1454_;
}
}
v___jp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = lean_array_fset(v_xs_x27_1453_, v_j_1445_, v___y_1455_);
lean_dec(v_j_1445_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1456_);
v___x_1458_ = v___x_1449_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
else
{
lean_object* v_ks_1486_; lean_object* v_vs_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1507_; 
v_ks_1486_ = lean_ctor_get(v_x_1435_, 0);
v_vs_1487_ = lean_ctor_get(v_x_1435_, 1);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_x_1435_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1489_ = v_x_1435_;
v_isShared_1490_ = v_isSharedCheck_1507_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_vs_1487_);
lean_inc(v_ks_1486_);
lean_dec(v_x_1435_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1507_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_ks_1486_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_vs_1487_);
v___x_1492_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v_newNode_1493_; uint8_t v___y_1495_; size_t v___x_1501_; uint8_t v___x_1502_; 
v_newNode_1493_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1492_, v_x_1438_, v_x_1439_);
v___x_1501_ = ((size_t)7ULL);
v___x_1502_ = lean_usize_dec_le(v___x_1501_, v_x_1437_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1503_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1493_);
v___x_1504_ = lean_unsigned_to_nat(4u);
v___x_1505_ = lean_nat_dec_lt(v___x_1503_, v___x_1504_);
lean_dec(v___x_1503_);
v___y_1495_ = v___x_1505_;
goto v___jp_1494_;
}
else
{
v___y_1495_ = v___x_1502_;
goto v___jp_1494_;
}
v___jp_1494_:
{
if (v___y_1495_ == 0)
{
lean_object* v_ks_1496_; lean_object* v_vs_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_ks_1496_ = lean_ctor_get(v_newNode_1493_, 0);
lean_inc_ref(v_ks_1496_);
v_vs_1497_ = lean_ctor_get(v_newNode_1493_, 1);
lean_inc_ref(v_vs_1497_);
lean_dec_ref(v_newNode_1493_);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1500_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1437_, v_ks_1496_, v_vs_1497_, v___x_1498_, v___x_1499_);
lean_dec_ref(v_vs_1497_);
lean_dec_ref(v_ks_1496_);
return v___x_1500_;
}
else
{
return v_newNode_1493_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1508_, lean_object* v_keys_1509_, lean_object* v_vals_1510_, lean_object* v_i_1511_, lean_object* v_entries_1512_){
_start:
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = lean_array_get_size(v_keys_1509_);
v___x_1514_ = lean_nat_dec_lt(v_i_1511_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_dec(v_i_1511_);
return v_entries_1512_;
}
else
{
lean_object* v_k_1515_; lean_object* v_v_1516_; uint64_t v___x_1517_; size_t v_h_1518_; size_t v___x_1519_; lean_object* v___x_1520_; size_t v___x_1521_; size_t v___x_1522_; size_t v___x_1523_; size_t v_h_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_k_1515_ = lean_array_fget_borrowed(v_keys_1509_, v_i_1511_);
v_v_1516_ = lean_array_fget_borrowed(v_vals_1510_, v_i_1511_);
v___x_1517_ = l_Lean_instHashableMVarId_hash(v_k_1515_);
v_h_1518_ = lean_uint64_to_usize(v___x_1517_);
v___x_1519_ = ((size_t)5ULL);
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = ((size_t)1ULL);
v___x_1522_ = lean_usize_sub(v_depth_1508_, v___x_1521_);
v___x_1523_ = lean_usize_mul(v___x_1519_, v___x_1522_);
v_h_1524_ = lean_usize_shift_right(v_h_1518_, v___x_1523_);
v___x_1525_ = lean_nat_add(v_i_1511_, v___x_1520_);
lean_dec(v_i_1511_);
lean_inc(v_v_1516_);
lean_inc(v_k_1515_);
v___x_1526_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1512_, v_h_1524_, v_depth_1508_, v_k_1515_, v_v_1516_);
v_i_1511_ = v___x_1525_;
v_entries_1512_ = v___x_1526_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1528_, lean_object* v_keys_1529_, lean_object* v_vals_1530_, lean_object* v_i_1531_, lean_object* v_entries_1532_){
_start:
{
size_t v_depth_boxed_1533_; lean_object* v_res_1534_; 
v_depth_boxed_1533_ = lean_unbox_usize(v_depth_1528_);
lean_dec(v_depth_1528_);
v_res_1534_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1533_, v_keys_1529_, v_vals_1530_, v_i_1531_, v_entries_1532_);
lean_dec_ref(v_vals_1530_);
lean_dec_ref(v_keys_1529_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1535_, lean_object* v_x_1536_, lean_object* v_x_1537_, lean_object* v_x_1538_, lean_object* v_x_1539_){
_start:
{
size_t v_x_865__boxed_1540_; size_t v_x_866__boxed_1541_; lean_object* v_res_1542_; 
v_x_865__boxed_1540_ = lean_unbox_usize(v_x_1536_);
lean_dec(v_x_1536_);
v_x_866__boxed_1541_ = lean_unbox_usize(v_x_1537_);
lean_dec(v_x_1537_);
v_res_1542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1535_, v_x_865__boxed_1540_, v_x_866__boxed_1541_, v_x_1538_, v_x_1539_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_){
_start:
{
uint64_t v___x_1546_; size_t v___x_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v___x_1546_ = l_Lean_instHashableMVarId_hash(v_x_1544_);
v___x_1547_ = lean_uint64_to_usize(v___x_1546_);
v___x_1548_ = ((size_t)1ULL);
v___x_1549_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1543_, v___x_1547_, v___x_1548_, v_x_1544_, v_x_1545_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1550_, lean_object* v_val_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; lean_object* v_mctx_1555_; lean_object* v_cache_1556_; lean_object* v_zetaDeltaFVarIds_1557_; lean_object* v_postponed_1558_; lean_object* v_diag_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1586_; 
v___x_1554_ = lean_st_ref_take(v___y_1552_);
v_mctx_1555_ = lean_ctor_get(v___x_1554_, 0);
v_cache_1556_ = lean_ctor_get(v___x_1554_, 1);
v_zetaDeltaFVarIds_1557_ = lean_ctor_get(v___x_1554_, 2);
v_postponed_1558_ = lean_ctor_get(v___x_1554_, 3);
v_diag_1559_ = lean_ctor_get(v___x_1554_, 4);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1561_ = v___x_1554_;
v_isShared_1562_ = v_isSharedCheck_1586_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_diag_1559_);
lean_inc(v_postponed_1558_);
lean_inc(v_zetaDeltaFVarIds_1557_);
lean_inc(v_cache_1556_);
lean_inc(v_mctx_1555_);
lean_dec(v___x_1554_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1586_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v_depth_1563_; lean_object* v_levelAssignDepth_1564_; lean_object* v_mvarCounter_1565_; lean_object* v_lDepth_1566_; lean_object* v_decls_1567_; lean_object* v_userNames_1568_; lean_object* v_lAssignment_1569_; lean_object* v_eAssignment_1570_; lean_object* v_dAssignment_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1585_; 
v_depth_1563_ = lean_ctor_get(v_mctx_1555_, 0);
v_levelAssignDepth_1564_ = lean_ctor_get(v_mctx_1555_, 1);
v_mvarCounter_1565_ = lean_ctor_get(v_mctx_1555_, 2);
v_lDepth_1566_ = lean_ctor_get(v_mctx_1555_, 3);
v_decls_1567_ = lean_ctor_get(v_mctx_1555_, 4);
v_userNames_1568_ = lean_ctor_get(v_mctx_1555_, 5);
v_lAssignment_1569_ = lean_ctor_get(v_mctx_1555_, 6);
v_eAssignment_1570_ = lean_ctor_get(v_mctx_1555_, 7);
v_dAssignment_1571_ = lean_ctor_get(v_mctx_1555_, 8);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_mctx_1555_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1573_ = v_mctx_1555_;
v_isShared_1574_ = v_isSharedCheck_1585_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_dAssignment_1571_);
lean_inc(v_eAssignment_1570_);
lean_inc(v_lAssignment_1569_);
lean_inc(v_userNames_1568_);
lean_inc(v_decls_1567_);
lean_inc(v_lDepth_1566_);
lean_inc(v_mvarCounter_1565_);
lean_inc(v_levelAssignDepth_1564_);
lean_inc(v_depth_1563_);
lean_dec(v_mctx_1555_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1585_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1575_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1570_, v_mvarId_1550_, v_val_1551_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 7, v___x_1575_);
v___x_1577_ = v___x_1573_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_depth_1563_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_levelAssignDepth_1564_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_mvarCounter_1565_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v_lDepth_1566_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v_decls_1567_);
lean_ctor_set(v_reuseFailAlloc_1584_, 5, v_userNames_1568_);
lean_ctor_set(v_reuseFailAlloc_1584_, 6, v_lAssignment_1569_);
lean_ctor_set(v_reuseFailAlloc_1584_, 7, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1584_, 8, v_dAssignment_1571_);
v___x_1577_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1579_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1577_);
v___x_1579_ = v___x_1561_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_cache_1556_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_zetaDeltaFVarIds_1557_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v_postponed_1558_);
lean_ctor_set(v_reuseFailAlloc_1583_, 4, v_diag_1559_);
v___x_1579_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = lean_st_ref_set(v___y_1552_, v___x_1579_);
v___x_1581_ = lean_box(0);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1587_, lean_object* v_val_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1587_, v_val_1588_, v___y_1589_);
lean_dec(v___y_1589_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; 
lean_inc(v_g_1592_);
v___x_1598_ = l_Lean_MVarId_getType(v_g_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = lean_box(0);
lean_inc(v___y_1594_);
v___x_1601_ = l_Lean_Meta_synthInstance(v_a_1599_, v___x_1600_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1611_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref(v___x_1601_);
v___x_1603_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1592_, v_a_1602_, v___y_1594_);
lean_dec(v___y_1594_);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v___x_1603_, 0);
lean_dec(v_unused_1612_);
v___x_1605_ = v___x_1603_;
v_isShared_1606_ = v_isSharedCheck_1611_;
goto v_resetjp_1604_;
}
else
{
lean_dec(v___x_1603_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1611_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = lean_box(0);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1607_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v___y_1594_);
lean_dec(v_g_1592_);
v_a_1613_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1601_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1601_);
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
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v_g_1592_);
v_a_1621_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1598_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1598_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1637_){
_start:
{
lean_object* v___f_1638_; lean_object* v___x_1639_; 
v___f_1638_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1639_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1637_, v___f_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1640_, lean_object* v_val_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1640_, v_val_1641_, v___y_1643_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1648_, lean_object* v_val_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1648_, v_val_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1657_, v_x_1658_, v_x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1661_, lean_object* v_x_1662_, size_t v_x_1663_, size_t v_x_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1662_, v_x_1663_, v_x_1664_, v_x_1665_, v_x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_, lean_object* v_x_1673_){
_start:
{
size_t v_x_1196__boxed_1674_; size_t v_x_1197__boxed_1675_; lean_object* v_res_1676_; 
v_x_1196__boxed_1674_ = lean_unbox_usize(v_x_1670_);
lean_dec(v_x_1670_);
v_x_1197__boxed_1675_ = lean_unbox_usize(v_x_1671_);
lean_dec(v_x_1671_);
v_res_1676_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1668_, v_x_1669_, v_x_1196__boxed_1674_, v_x_1197__boxed_1675_, v_x_1672_, v_x_1673_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1677_, lean_object* v_n_1678_, lean_object* v_k_1679_, lean_object* v_v_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1678_, v_k_1679_, v_v_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1682_, size_t v_depth_1683_, lean_object* v_keys_1684_, lean_object* v_vals_1685_, lean_object* v_heq_1686_, lean_object* v_i_1687_, lean_object* v_entries_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1683_, v_keys_1684_, v_vals_1685_, v_i_1687_, v_entries_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1690_, lean_object* v_depth_1691_, lean_object* v_keys_1692_, lean_object* v_vals_1693_, lean_object* v_heq_1694_, lean_object* v_i_1695_, lean_object* v_entries_1696_){
_start:
{
size_t v_depth_boxed_1697_; lean_object* v_res_1698_; 
v_depth_boxed_1697_ = lean_unbox_usize(v_depth_1691_);
lean_dec(v_depth_1691_);
v_res_1698_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1690_, v_depth_boxed_1697_, v_keys_1692_, v_vals_1693_, v_heq_1694_, v_i_1695_, v_entries_1696_);
lean_dec_ref(v_vals_1693_);
lean_dec_ref(v_keys_1692_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1700_, v_x_1701_, v_x_1702_, v_x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1705_, lean_object* v_discharge_1706_, lean_object* v_g_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
lean_inc(v___y_1711_);
lean_inc_ref(v___y_1710_);
lean_inc(v___y_1709_);
lean_inc_ref(v___y_1708_);
lean_inc(v_g_1707_);
v___x_1713_ = lean_apply_6(v_discharge_1705_, v_g_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, lean_box(0));
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v_g_1707_);
lean_dec_ref(v_discharge_1706_);
return v___x_1713_;
}
else
{
lean_object* v_a_1714_; uint8_t v___y_1716_; uint8_t v___x_1718_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
v___x_1718_ = l_Lean_Exception_isInterrupt(v_a_1714_);
if (v___x_1718_ == 0)
{
uint8_t v___x_1719_; 
v___x_1719_ = l_Lean_Exception_isRuntime(v_a_1714_);
v___y_1716_ = v___x_1719_;
goto v___jp_1715_;
}
else
{
lean_dec(v_a_1714_);
v___y_1716_ = v___x_1718_;
goto v___jp_1715_;
}
v___jp_1715_:
{
if (v___y_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec_ref(v___x_1713_);
v___x_1717_ = lean_apply_6(v_discharge_1706_, v_g_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, lean_box(0));
return v___x_1717_;
}
else
{
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v_g_1707_);
lean_dec_ref(v_discharge_1706_);
return v___x_1713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1720_, lean_object* v_discharge_1721_, lean_object* v_g_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1720_, v_discharge_1721_, v_g_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1729_, lean_object* v_discharge_1730_){
_start:
{
lean_object* v_toApplyRulesConfig_1731_; lean_object* v_toBacktrackConfig_1732_; uint8_t v_backtracking_1733_; uint8_t v_intro_1734_; uint8_t v_constructor_1735_; uint8_t v_suggestions_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1768_; 
v_toApplyRulesConfig_1731_ = lean_ctor_get(v_cfg_1729_, 0);
lean_inc_ref(v_toApplyRulesConfig_1731_);
v_toBacktrackConfig_1732_ = lean_ctor_get(v_toApplyRulesConfig_1731_, 0);
lean_inc_ref(v_toBacktrackConfig_1732_);
v_backtracking_1733_ = lean_ctor_get_uint8(v_cfg_1729_, sizeof(void*)*1);
v_intro_1734_ = lean_ctor_get_uint8(v_cfg_1729_, sizeof(void*)*1 + 1);
v_constructor_1735_ = lean_ctor_get_uint8(v_cfg_1729_, sizeof(void*)*1 + 2);
v_suggestions_1736_ = lean_ctor_get_uint8(v_cfg_1729_, sizeof(void*)*1 + 3);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_cfg_1729_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v_cfg_1729_, 0);
lean_dec(v_unused_1769_);
v___x_1738_ = v_cfg_1729_;
v_isShared_1739_ = v_isSharedCheck_1768_;
goto v_resetjp_1737_;
}
else
{
lean_dec(v_cfg_1729_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1768_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v_toApplyConfig_1740_; uint8_t v_transparency_1741_; uint8_t v_symm_1742_; uint8_t v_exfalso_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1766_; 
v_toApplyConfig_1740_ = lean_ctor_get(v_toApplyRulesConfig_1731_, 1);
v_transparency_1741_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1731_, sizeof(void*)*2);
v_symm_1742_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1731_, sizeof(void*)*2 + 1);
v_exfalso_1743_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1731_, sizeof(void*)*2 + 2);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_toApplyRulesConfig_1731_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; 
v_unused_1767_ = lean_ctor_get(v_toApplyRulesConfig_1731_, 0);
lean_dec(v_unused_1767_);
v___x_1745_ = v_toApplyRulesConfig_1731_;
v_isShared_1746_ = v_isSharedCheck_1766_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_toApplyConfig_1740_);
lean_dec(v_toApplyRulesConfig_1731_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1766_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v_maxDepth_1747_; lean_object* v_proc_1748_; lean_object* v_suspend_1749_; lean_object* v_discharge_1750_; uint8_t v_commitIndependentGoals_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1765_; 
v_maxDepth_1747_ = lean_ctor_get(v_toBacktrackConfig_1732_, 0);
v_proc_1748_ = lean_ctor_get(v_toBacktrackConfig_1732_, 1);
v_suspend_1749_ = lean_ctor_get(v_toBacktrackConfig_1732_, 2);
v_discharge_1750_ = lean_ctor_get(v_toBacktrackConfig_1732_, 3);
v_commitIndependentGoals_1751_ = lean_ctor_get_uint8(v_toBacktrackConfig_1732_, sizeof(void*)*4);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_toBacktrackConfig_1732_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1753_ = v_toBacktrackConfig_1732_;
v_isShared_1754_ = v_isSharedCheck_1765_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_discharge_1750_);
lean_inc(v_suspend_1749_);
lean_inc(v_proc_1748_);
lean_inc(v_maxDepth_1747_);
lean_dec(v_toBacktrackConfig_1732_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1765_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___f_1755_; lean_object* v___x_1757_; 
v___f_1755_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1755_, 0, v_discharge_1730_);
lean_closure_set(v___f_1755_, 1, v_discharge_1750_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 3, v___f_1755_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_maxDepth_1747_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_proc_1748_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_suspend_1749_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v___f_1755_);
lean_ctor_set_uint8(v_reuseFailAlloc_1764_, sizeof(void*)*4, v_commitIndependentGoals_1751_);
v___x_1757_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1759_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1757_);
v___x_1759_ = v___x_1745_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_toApplyConfig_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1763_, sizeof(void*)*2, v_transparency_1741_);
lean_ctor_set_uint8(v_reuseFailAlloc_1763_, sizeof(void*)*2 + 1, v_symm_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1763_, sizeof(void*)*2 + 2, v_exfalso_1743_);
v___x_1759_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1761_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1759_);
v___x_1761_ = v___x_1738_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, sizeof(void*)*1, v_backtracking_1733_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, sizeof(void*)*1 + 1, v_intro_1734_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, sizeof(void*)*1 + 2, v_constructor_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, sizeof(void*)*1 + 3, v_suggestions_1736_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
uint8_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = 1;
v___x_1777_ = l_Lean_Meta_intro1Core(v_g_1770_, v___x_1776_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1796_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1796_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1796_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_snd_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1794_; 
v_snd_1782_ = lean_ctor_get(v_a_1778_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_a_1778_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v_a_1778_, 0);
lean_dec(v_unused_1795_);
v___x_1784_ = v_a_1778_;
v_isShared_1785_ = v_isSharedCheck_1794_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_snd_1782_);
lean_dec(v_a_1778_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1794_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1786_ = lean_box(0);
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 1);
lean_ctor_set(v___x_1784_, 1, v___x_1786_);
lean_ctor_set(v___x_1784_, 0, v_snd_1782_);
v___x_1788_ = v___x_1784_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_snd_1782_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1789_);
v___x_1791_ = v___x_1780_;
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
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
v_a_1797_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1777_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1777_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1813_){
_start:
{
lean_object* v___f_1814_; lean_object* v___x_1815_; 
v___f_1814_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1815_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1813_, v___f_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1827_ = l_Lean_MVarId_constructor(v_g_1820_, v___x_1826_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1836_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_a_1828_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1832_);
v___x_1834_ = v___x_1830_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
v_a_1837_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1827_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1827_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1853_){
_start:
{
lean_object* v___f_1854_; lean_object* v___x_1855_; 
v___f_1854_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1855_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1853_, v___f_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; 
lean_inc(v_g_1858_);
v___x_1864_ = l_Lean_MVarId_getType(v_g_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v___x_1864_);
v___x_1866_ = lean_box(0);
lean_inc(v___y_1860_);
v___x_1867_ = l_Lean_Meta_synthInstance(v_a_1865_, v___x_1866_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1877_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref(v___x_1867_);
v___x_1869_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1858_, v_a_1868_, v___y_1860_);
lean_dec(v___y_1860_);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1877_ == 0)
{
lean_object* v_unused_1878_; 
v_unused_1878_ = lean_ctor_get(v___x_1869_, 0);
lean_dec(v_unused_1878_);
v___x_1871_ = v___x_1869_;
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
else
{
lean_dec(v___x_1869_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1873_);
v___x_1875_ = v___x_1871_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v___y_1860_);
lean_dec(v_g_1858_);
v_a_1879_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1867_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1867_);
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
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_g_1858_);
v_a_1887_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1864_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1864_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1903_){
_start:
{
lean_object* v___f_1904_; lean_object* v___x_1905_; 
v___f_1904_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1905_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1903_, v___f_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1906_, lean_object* v___y_1907_){
_start:
{
uint8_t v___x_1909_; 
v___x_1909_ = l_Lean_Expr_hasMVar(v_e_1906_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v_e_1906_);
return v___x_1910_;
}
else
{
lean_object* v___x_1911_; lean_object* v_mctx_1912_; lean_object* v___x_1913_; lean_object* v_fst_1914_; lean_object* v_snd_1915_; lean_object* v___x_1916_; lean_object* v_cache_1917_; lean_object* v_zetaDeltaFVarIds_1918_; lean_object* v_postponed_1919_; lean_object* v_diag_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1929_; 
v___x_1911_ = lean_st_ref_get(v___y_1907_);
v_mctx_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc_ref(v_mctx_1912_);
lean_dec(v___x_1911_);
v___x_1913_ = l_Lean_instantiateMVarsCore(v_mctx_1912_, v_e_1906_);
v_fst_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_fst_1914_);
v_snd_1915_ = lean_ctor_get(v___x_1913_, 1);
lean_inc(v_snd_1915_);
lean_dec_ref(v___x_1913_);
v___x_1916_ = lean_st_ref_take(v___y_1907_);
v_cache_1917_ = lean_ctor_get(v___x_1916_, 1);
v_zetaDeltaFVarIds_1918_ = lean_ctor_get(v___x_1916_, 2);
v_postponed_1919_ = lean_ctor_get(v___x_1916_, 3);
v_diag_1920_ = lean_ctor_get(v___x_1916_, 4);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; 
v_unused_1930_ = lean_ctor_get(v___x_1916_, 0);
lean_dec(v_unused_1930_);
v___x_1922_ = v___x_1916_;
v_isShared_1923_ = v_isSharedCheck_1929_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_diag_1920_);
lean_inc(v_postponed_1919_);
lean_inc(v_zetaDeltaFVarIds_1918_);
lean_inc(v_cache_1917_);
lean_dec(v___x_1916_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1929_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v_snd_1915_);
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_snd_1915_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_cache_1917_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_zetaDeltaFVarIds_1918_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_postponed_1919_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_diag_1920_);
v___x_1925_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_st_ref_set(v___y_1907_, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_fst_1914_);
return v___x_1927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1931_, v___y_1932_);
lean_dec(v___y_1932_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1935_, v___y_1937_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1949_, lean_object* v_x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1949_, v_x_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
v_a_1965_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1956_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1956_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1973_, lean_object* v_x_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1973_, v_x_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1981_, lean_object* v_mvarId_1982_, lean_object* v_x_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1982_, v_x_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1990_, lean_object* v_mvarId_1991_, lean_object* v_x_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1990_, v_mvarId_1991_, v_x_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_ref_2005_; lean_object* v___x_2006_; lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2015_; 
v_ref_2005_ = lean_ctor_get(v___y_2002_, 5);
v___x_2006_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__8(v_msg_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2015_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2015_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
lean_inc(v_ref_2005_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v_ref_2005_);
lean_ctor_set(v___x_2011_, 1, v_a_2007_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set_tag(v___x_2009_, 1);
lean_ctor_set(v___x_2009_, 0, v___x_2011_);
v___x_2013_ = v___x_2009_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_2023_, lean_object* v_x_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
if (lean_obj_tag(v_x_2023_) == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
v___x_2030_ = l_List_reverse___redArg(v_x_2024_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
return v___x_2031_;
}
else
{
lean_object* v_head_2032_; lean_object* v_tail_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2053_; 
v_head_2032_ = lean_ctor_get(v_x_2023_, 0);
v_tail_2033_ = lean_ctor_get(v_x_2023_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_x_2023_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2035_ = v_x_2023_;
v_isShared_2036_ = v_isSharedCheck_2053_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_tail_2033_);
lean_inc(v_head_2032_);
lean_dec(v_x_2023_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2053_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_inc(v_head_2032_);
v___x_2037_ = l_Lean_Expr_mvar___override(v_head_2032_);
v___x_2038_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_2038_, 0, v___x_2037_);
lean_inc(v___y_2028_);
lean_inc_ref(v___y_2027_);
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
v___x_2039_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_2032_, v___x_2038_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref(v___x_2039_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v_x_2024_);
lean_ctor_set(v___x_2035_, 0, v_a_2040_);
v___x_2042_ = v___x_2035_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2040_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_x_2024_);
v___x_2042_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
v_x_2023_ = v_tail_2033_;
v_x_2024_ = v___x_2042_;
goto _start;
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_del_object(v___x_2035_);
lean_dec(v_tail_2033_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v_x_2024_);
v_a_2045_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2039_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2039_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_2054_, lean_object* v_x_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_2054_, v_x_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
return v_res_2061_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_2064_ = l_Lean_stringToMessageData(v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_2065_, lean_object* v_proc_2066_, lean_object* v_orig_2067_, lean_object* v_goals_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_box(0);
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2069_);
lean_inc(v_orig_2067_);
v___x_2075_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_2067_, v___x_2074_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2077_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref(v___x_2075_);
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2069_);
v___x_2077_ = lean_apply_6(v_test_2065_, v_a_2076_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, lean_box(0));
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; uint8_t v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2077_);
v___x_2079_ = lean_unbox(v_a_2078_);
lean_dec(v_a_2078_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_goals_2068_);
lean_dec(v_orig_2067_);
lean_dec_ref(v_proc_2066_);
v___x_2080_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_2081_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2080_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
else
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_apply_7(v_proc_2066_, v_orig_2067_, v_goals_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, lean_box(0));
return v___x_2090_;
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v_goals_2068_);
lean_dec(v_orig_2067_);
lean_dec_ref(v_proc_2066_);
v_a_2091_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2077_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2077_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v_goals_2068_);
lean_dec(v_orig_2067_);
lean_dec_ref(v_proc_2066_);
lean_dec_ref(v_test_2065_);
v_a_2099_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2075_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2075_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_2107_, lean_object* v_proc_2108_, lean_object* v_orig_2109_, lean_object* v_goals_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_2107_, v_proc_2108_, v_orig_2109_, v_goals_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_2117_, lean_object* v_test_2118_){
_start:
{
lean_object* v_toApplyRulesConfig_2119_; lean_object* v_toBacktrackConfig_2120_; uint8_t v_backtracking_2121_; uint8_t v_intro_2122_; uint8_t v_constructor_2123_; uint8_t v_suggestions_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2156_; 
v_toApplyRulesConfig_2119_ = lean_ctor_get(v_cfg_2117_, 0);
lean_inc_ref(v_toApplyRulesConfig_2119_);
v_toBacktrackConfig_2120_ = lean_ctor_get(v_toApplyRulesConfig_2119_, 0);
lean_inc_ref(v_toBacktrackConfig_2120_);
v_backtracking_2121_ = lean_ctor_get_uint8(v_cfg_2117_, sizeof(void*)*1);
v_intro_2122_ = lean_ctor_get_uint8(v_cfg_2117_, sizeof(void*)*1 + 1);
v_constructor_2123_ = lean_ctor_get_uint8(v_cfg_2117_, sizeof(void*)*1 + 2);
v_suggestions_2124_ = lean_ctor_get_uint8(v_cfg_2117_, sizeof(void*)*1 + 3);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_cfg_2117_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; 
v_unused_2157_ = lean_ctor_get(v_cfg_2117_, 0);
lean_dec(v_unused_2157_);
v___x_2126_ = v_cfg_2117_;
v_isShared_2127_ = v_isSharedCheck_2156_;
goto v_resetjp_2125_;
}
else
{
lean_dec(v_cfg_2117_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2156_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_toApplyConfig_2128_; uint8_t v_transparency_2129_; uint8_t v_symm_2130_; uint8_t v_exfalso_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2154_; 
v_toApplyConfig_2128_ = lean_ctor_get(v_toApplyRulesConfig_2119_, 1);
v_transparency_2129_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2119_, sizeof(void*)*2);
v_symm_2130_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2119_, sizeof(void*)*2 + 1);
v_exfalso_2131_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2119_, sizeof(void*)*2 + 2);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_toApplyRulesConfig_2119_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v_toApplyRulesConfig_2119_, 0);
lean_dec(v_unused_2155_);
v___x_2133_ = v_toApplyRulesConfig_2119_;
v_isShared_2134_ = v_isSharedCheck_2154_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_toApplyConfig_2128_);
lean_dec(v_toApplyRulesConfig_2119_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2154_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_maxDepth_2135_; lean_object* v_proc_2136_; lean_object* v_suspend_2137_; lean_object* v_discharge_2138_; uint8_t v_commitIndependentGoals_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2153_; 
v_maxDepth_2135_ = lean_ctor_get(v_toBacktrackConfig_2120_, 0);
v_proc_2136_ = lean_ctor_get(v_toBacktrackConfig_2120_, 1);
v_suspend_2137_ = lean_ctor_get(v_toBacktrackConfig_2120_, 2);
v_discharge_2138_ = lean_ctor_get(v_toBacktrackConfig_2120_, 3);
v_commitIndependentGoals_2139_ = lean_ctor_get_uint8(v_toBacktrackConfig_2120_, sizeof(void*)*4);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_toBacktrackConfig_2120_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2141_ = v_toBacktrackConfig_2120_;
v_isShared_2142_ = v_isSharedCheck_2153_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_discharge_2138_);
lean_inc(v_suspend_2137_);
lean_inc(v_proc_2136_);
lean_inc(v_maxDepth_2135_);
lean_dec(v_toBacktrackConfig_2120_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2153_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___f_2143_; lean_object* v___x_2145_; 
v___f_2143_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2143_, 0, v_test_2118_);
lean_closure_set(v___f_2143_, 1, v_proc_2136_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 1, v___f_2143_);
v___x_2145_ = v___x_2141_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_maxDepth_2135_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v___f_2143_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_suspend_2137_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_discharge_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2152_, sizeof(void*)*4, v_commitIndependentGoals_2139_);
v___x_2145_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2145_);
v___x_2147_ = v___x_2133_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_toApplyConfig_2128_);
lean_ctor_set_uint8(v_reuseFailAlloc_2151_, sizeof(void*)*2, v_transparency_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2151_, sizeof(void*)*2 + 1, v_symm_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2151_, sizeof(void*)*2 + 2, v_exfalso_2131_);
v___x_2147_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2149_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2147_);
v___x_2149_ = v___x_2126_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2150_, sizeof(void*)*1, v_backtracking_2121_);
lean_ctor_set_uint8(v_reuseFailAlloc_2150_, sizeof(void*)*1 + 1, v_intro_2122_);
lean_ctor_set_uint8(v_reuseFailAlloc_2150_, sizeof(void*)*1 + 2, v_constructor_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2150_, sizeof(void*)*1 + 3, v_suggestions_2124_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2158_, lean_object* v_msg_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2166_, lean_object* v_msg_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2166_, v_msg_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2175_, lean_object* v_sols_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___closed__0));
lean_inc(v_sols_2176_);
v___x_2183_ = l_List_any___redArg(v_sols_2176_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_apply_6(v_test_2175_, v_sols_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, lean_box(0));
return v___x_2184_;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v_sols_2176_);
lean_dec_ref(v_test_2175_);
v___x_2185_ = lean_box(v___x_2183_);
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
return v___x_2186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2187_, lean_object* v_sols_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2187_, v_sols_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2195_, lean_object* v_test_2196_){
_start:
{
lean_object* v___f_2197_; lean_object* v___x_2198_; 
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2197_, 0, v_test_2196_);
v___x_2198_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2195_, v___f_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_e_2199_, lean_object* v_s_2200_){
_start:
{
uint8_t v___x_2201_; 
v___x_2201_ = l_Lean_Expr_occurs(v_e_2199_, v_s_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_e_2202_, lean_object* v_s_2203_){
_start:
{
uint8_t v_res_2204_; lean_object* v_r_2205_; 
v_res_2204_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_e_2202_, v_s_2203_);
lean_dec_ref(v_s_2203_);
v_r_2205_ = lean_box(v_res_2204_);
return v_r_2205_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(lean_object* v_sols_2206_, lean_object* v_e_2207_){
_start:
{
lean_object* v___f_2208_; uint8_t v___x_2209_; 
v___f_2208_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2208_, 0, v_e_2207_);
v___x_2209_ = l_List_any___redArg(v_sols_2206_, v___f_2208_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed(lean_object* v_sols_2210_, lean_object* v_e_2211_){
_start:
{
uint8_t v_res_2212_; lean_object* v_r_2213_; 
v_res_2212_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(v_sols_2210_, v_e_2211_);
v_r_2213_ = lean_box(v_res_2212_);
return v_r_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(lean_object* v_use_2214_, lean_object* v_sols_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___f_2221_; uint8_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___f_2221_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2221_, 0, v_sols_2215_);
v___x_2222_ = l_List_all___redArg(v_use_2214_, v___f_2221_);
v___x_2223_ = lean_box(v___x_2222_);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed(lean_object* v_use_2225_, lean_object* v_sols_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(v_use_2225_, v_sols_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2233_, lean_object* v_use_2234_){
_start:
{
lean_object* v___f_2235_; lean_object* v___x_2236_; 
v___f_2235_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2235_, 0, v_use_2234_);
v___x_2236_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2233_, v___f_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2237_){
_start:
{
lean_object* v___y_2239_; lean_object* v_toApplyRulesConfig_2240_; uint8_t v_backtracking_2241_; uint8_t v_intro_2242_; uint8_t v_constructor_2243_; uint8_t v_suggestions_2244_; uint8_t v_intro_2248_; 
v_intro_2248_ = lean_ctor_get_uint8(v_cfg_2237_, sizeof(void*)*1 + 1);
if (v_intro_2248_ == 0)
{
lean_object* v_toApplyRulesConfig_2249_; uint8_t v_backtracking_2250_; uint8_t v_constructor_2251_; uint8_t v_suggestions_2252_; 
v_toApplyRulesConfig_2249_ = lean_ctor_get(v_cfg_2237_, 0);
lean_inc_ref(v_toApplyRulesConfig_2249_);
v_backtracking_2250_ = lean_ctor_get_uint8(v_cfg_2237_, sizeof(void*)*1);
v_constructor_2251_ = lean_ctor_get_uint8(v_cfg_2237_, sizeof(void*)*1 + 2);
v_suggestions_2252_ = lean_ctor_get_uint8(v_cfg_2237_, sizeof(void*)*1 + 3);
v___y_2239_ = v_cfg_2237_;
v_toApplyRulesConfig_2240_ = v_toApplyRulesConfig_2249_;
v_backtracking_2241_ = v_backtracking_2250_;
v_intro_2242_ = v_intro_2248_;
v_constructor_2243_ = v_constructor_2251_;
v_suggestions_2244_ = v_suggestions_2252_;
goto v___jp_2238_;
}
else
{
lean_object* v_toApplyRulesConfig_2253_; uint8_t v_backtracking_2254_; uint8_t v_constructor_2255_; uint8_t v_suggestions_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2270_; 
v_toApplyRulesConfig_2253_ = lean_ctor_get(v_cfg_2237_, 0);
v_backtracking_2254_ = lean_ctor_get_uint8(v_cfg_2237_, sizeof(void*)*1);
v_constructor_2255_ = lean_ctor_get_uint8(v_cfg_2237_, sizeof(void*)*1 + 2);
v_suggestions_2256_ = lean_ctor_get_uint8(v_cfg_2237_, sizeof(void*)*1 + 3);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_cfg_2237_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2258_ = v_cfg_2237_;
v_isShared_2259_ = v_isSharedCheck_2270_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_toApplyRulesConfig_2253_);
lean_dec(v_cfg_2237_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2270_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
uint8_t v___x_2260_; lean_object* v___x_2262_; 
v___x_2260_ = 0;
if (v_isShared_2259_ == 0)
{
v___x_2262_ = v___x_2258_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_toApplyRulesConfig_2253_);
lean_ctor_set_uint8(v_reuseFailAlloc_2269_, sizeof(void*)*1, v_backtracking_2254_);
lean_ctor_set_uint8(v_reuseFailAlloc_2269_, sizeof(void*)*1 + 2, v_constructor_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2269_, sizeof(void*)*1 + 3, v_suggestions_2256_);
v___x_2262_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; lean_object* v_toApplyRulesConfig_2264_; uint8_t v_backtracking_2265_; uint8_t v_intro_2266_; uint8_t v_constructor_2267_; uint8_t v_suggestions_2268_; 
lean_ctor_set_uint8(v___x_2262_, sizeof(void*)*1 + 1, v___x_2260_);
v___x_2263_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2262_);
v_toApplyRulesConfig_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc_ref(v_toApplyRulesConfig_2264_);
v_backtracking_2265_ = lean_ctor_get_uint8(v___x_2263_, sizeof(void*)*1);
v_intro_2266_ = lean_ctor_get_uint8(v___x_2263_, sizeof(void*)*1 + 1);
v_constructor_2267_ = lean_ctor_get_uint8(v___x_2263_, sizeof(void*)*1 + 2);
v_suggestions_2268_ = lean_ctor_get_uint8(v___x_2263_, sizeof(void*)*1 + 3);
v___y_2239_ = v___x_2263_;
v_toApplyRulesConfig_2240_ = v_toApplyRulesConfig_2264_;
v_backtracking_2241_ = v_backtracking_2265_;
v_intro_2242_ = v_intro_2266_;
v_constructor_2243_ = v_constructor_2267_;
v_suggestions_2244_ = v_suggestions_2268_;
goto v___jp_2238_;
}
}
}
v___jp_2238_:
{
if (v_constructor_2243_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2240_);
return v___y_2239_;
}
else
{
uint8_t v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
lean_dec_ref(v___y_2239_);
v___x_2245_ = 0;
v___x_2246_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2246_, 0, v_toApplyRulesConfig_2240_);
lean_ctor_set_uint8(v___x_2246_, sizeof(void*)*1, v_backtracking_2241_);
lean_ctor_set_uint8(v___x_2246_, sizeof(void*)*1 + 1, v_intro_2242_);
lean_ctor_set_uint8(v___x_2246_, sizeof(void*)*1 + 2, v___x_2245_);
lean_ctor_set_uint8(v___x_2246_, sizeof(void*)*1 + 3, v_suggestions_2244_);
v___x_2247_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2246_);
return v___x_2247_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2271_, lean_object* v_x_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
if (lean_obj_tag(v_x_2271_) == 0)
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
v___x_2280_ = l_List_reverse___redArg(v_x_2272_);
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
return v___x_2281_;
}
else
{
lean_object* v_head_2282_; lean_object* v_tail_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2301_; 
v_head_2282_ = lean_ctor_get(v_x_2271_, 0);
v_tail_2283_ = lean_ctor_get(v_x_2271_, 1);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_x_2271_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2285_ = v_x_2271_;
v_isShared_2286_ = v_isSharedCheck_2301_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_tail_2283_);
lean_inc(v_head_2282_);
lean_dec(v_x_2271_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2301_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; 
lean_inc(v___y_2278_);
lean_inc_ref(v___y_2277_);
lean_inc(v___y_2276_);
lean_inc_ref(v___y_2275_);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2273_);
v___x_2287_ = lean_apply_7(v_head_2282_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, lean_box(0));
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2290_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref(v___x_2287_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v_x_2272_);
lean_ctor_set(v___x_2285_, 0, v_a_2288_);
v___x_2290_ = v___x_2285_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2288_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_x_2272_);
v___x_2290_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
v_x_2271_ = v_tail_2283_;
v_x_2272_ = v___x_2290_;
goto _start;
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_del_object(v___x_2285_);
lean_dec(v_tail_2283_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v_x_2272_);
v_a_2293_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2287_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2287_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2302_, lean_object* v_x_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2302_, v_x_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2312_, lean_object* v_cfg_2313_, lean_object* v_lemmas_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; 
lean_inc(v___y_2320_);
lean_inc_ref(v___y_2319_);
lean_inc(v___y_2318_);
lean_inc_ref(v___y_2317_);
lean_inc(v___y_2316_);
lean_inc_ref(v___y_2315_);
v___x_2322_ = lean_apply_8(v_ctx_2312_, v_cfg_2313_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, lean_box(0));
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref(v___x_2322_);
v___x_2324_ = lean_box(0);
v___x_2325_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2314_, v___x_2324_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2334_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2330_ = l_List_appendTR___redArg(v_a_2323_, v_a_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2330_);
v___x_2332_ = v___x_2328_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
else
{
lean_dec(v_a_2323_);
return v___x_2325_;
}
}
else
{
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v_lemmas_2314_);
return v___x_2322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2335_, lean_object* v_cfg_2336_, lean_object* v_lemmas_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2335_, v_cfg_2336_, v_lemmas_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
return v_res_2345_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2346_){
_start:
{
uint8_t v___x_2347_; 
v___x_2347_ = 0;
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2348_){
_start:
{
uint8_t v_res_2349_; lean_object* v_r_2350_; 
v_res_2349_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2348_);
lean_dec(v_x_2348_);
v_r_2350_ = lean_box(v_res_2349_);
return v_r_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2351_, lean_object* v___x_2352_, lean_object* v___x_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2351_, v___x_2352_, v___x_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2368_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2362_ = v___x_2359_;
v_isShared_2363_ = v_isSharedCheck_2368_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2368_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v_fst_2364_; lean_object* v___x_2366_; 
v_fst_2364_ = lean_ctor_get(v_a_2360_, 0);
lean_inc(v_fst_2364_);
lean_dec(v_a_2360_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v_fst_2364_);
v___x_2366_ = v___x_2362_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_fst_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_a_2369_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2359_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2359_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2377_, lean_object* v___x_2378_, lean_object* v___x_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2377_, v___x_2378_, v___x_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2400_, lean_object* v_g_2401_, lean_object* v_lemmas_2402_, lean_object* v_ctx_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___f_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___f_2412_; lean_object* v___x_2413_; 
v___f_2409_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2409_, 0, v_ctx_2403_);
lean_closure_set(v___f_2409_, 1, v_cfg_2400_);
lean_closure_set(v___f_2409_, 2, v_lemmas_2402_);
v___x_2410_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2411_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2412_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2412_, 0, v___f_2409_);
lean_closure_set(v___f_2412_, 1, v___x_2410_);
lean_closure_set(v___f_2412_, 2, v___x_2411_);
v___x_2413_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2401_, v___f_2412_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2414_, lean_object* v_g_2415_, lean_object* v_lemmas_2416_, lean_object* v_ctx_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2414_, v_g_2415_, v_lemmas_2416_, v_ctx_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2424_, lean_object* v_lemmas_2425_, lean_object* v_ctx_2426_, lean_object* v_g_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v___x_2433_; 
lean_inc(v_a_2431_);
lean_inc(v_a_2429_);
lean_inc(v_g_2427_);
lean_inc_ref(v_cfg_2424_);
v___x_2433_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2424_, v_g_2427_, v_lemmas_2425_, v_ctx_2426_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_toApplyRulesConfig_2434_; lean_object* v_a_2435_; lean_object* v_toApplyConfig_2436_; uint8_t v_transparency_2437_; lean_object* v___x_2438_; 
v_toApplyRulesConfig_2434_ = lean_ctor_get(v_cfg_2424_, 0);
lean_inc_ref(v_toApplyRulesConfig_2434_);
lean_dec_ref(v_cfg_2424_);
v_a_2435_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2435_);
lean_dec_ref(v___x_2433_);
v_toApplyConfig_2436_ = lean_ctor_get(v_toApplyRulesConfig_2434_, 1);
lean_inc_ref(v_toApplyConfig_2436_);
v_transparency_2437_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2434_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2434_);
v___x_2438_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2436_, v_transparency_2437_, v_a_2435_, v_g_2427_, v_a_2429_, v_a_2431_);
lean_dec(v_a_2431_);
lean_dec(v_a_2429_);
return v___x_2438_;
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec(v_a_2431_);
lean_dec(v_a_2429_);
lean_dec(v_g_2427_);
lean_dec_ref(v_cfg_2424_);
v_a_2439_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2433_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2433_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2447_, lean_object* v_lemmas_2448_, lean_object* v_ctx_2449_, lean_object* v_g_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2447_, v_lemmas_2448_, v_ctx_2449_, v_g_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2457_, lean_object* v_lemmas_2458_, lean_object* v_ctx_2459_, lean_object* v_g_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v___x_2466_; 
lean_inc(v_a_2464_);
lean_inc_ref(v_a_2463_);
lean_inc(v_a_2462_);
lean_inc_ref(v_a_2461_);
lean_inc(v_g_2460_);
lean_inc_ref(v_cfg_2457_);
v___x_2466_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2457_, v_g_2460_, v_lemmas_2458_, v_ctx_2459_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_toApplyRulesConfig_2467_; lean_object* v_a_2468_; lean_object* v_toApplyConfig_2469_; uint8_t v_transparency_2470_; lean_object* v___x_2471_; 
v_toApplyRulesConfig_2467_ = lean_ctor_get(v_cfg_2457_, 0);
lean_inc_ref(v_toApplyRulesConfig_2467_);
lean_dec_ref(v_cfg_2457_);
v_a_2468_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2468_);
lean_dec_ref(v___x_2466_);
v_toApplyConfig_2469_ = lean_ctor_get(v_toApplyRulesConfig_2467_, 1);
lean_inc_ref(v_toApplyConfig_2469_);
v_transparency_2470_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2467_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2467_);
v___x_2471_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2469_, v_transparency_2470_, v_a_2468_, v_g_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_);
return v___x_2471_;
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
lean_dec(v_g_2460_);
lean_dec_ref(v_cfg_2457_);
v_a_2472_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2466_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2466_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2480_, lean_object* v_lemmas_2481_, lean_object* v_ctx_2482_, lean_object* v_g_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2480_, v_lemmas_2481_, v_ctx_2482_, v_g_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
return v_res_2489_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2490_, lean_object* v_i_2491_, lean_object* v_k_2492_){
_start:
{
lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = lean_array_get_size(v_keys_2490_);
v___x_2494_ = lean_nat_dec_lt(v_i_2491_, v___x_2493_);
if (v___x_2494_ == 0)
{
lean_dec(v_i_2491_);
return v___x_2494_;
}
else
{
lean_object* v_k_x27_2495_; uint8_t v___x_2496_; 
v_k_x27_2495_ = lean_array_fget_borrowed(v_keys_2490_, v_i_2491_);
v___x_2496_ = l_Lean_instBEqMVarId_beq(v_k_2492_, v_k_x27_2495_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_unsigned_to_nat(1u);
v___x_2498_ = lean_nat_add(v_i_2491_, v___x_2497_);
lean_dec(v_i_2491_);
v_i_2491_ = v___x_2498_;
goto _start;
}
else
{
lean_dec(v_i_2491_);
return v___x_2496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2500_, lean_object* v_i_2501_, lean_object* v_k_2502_){
_start:
{
uint8_t v_res_2503_; lean_object* v_r_2504_; 
v_res_2503_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2500_, v_i_2501_, v_k_2502_);
lean_dec(v_k_2502_);
lean_dec_ref(v_keys_2500_);
v_r_2504_ = lean_box(v_res_2503_);
return v_r_2504_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2505_, size_t v_x_2506_, lean_object* v_x_2507_){
_start:
{
if (lean_obj_tag(v_x_2505_) == 0)
{
lean_object* v_es_2508_; lean_object* v___x_2509_; size_t v___x_2510_; size_t v___x_2511_; size_t v___x_2512_; lean_object* v_j_2513_; lean_object* v___x_2514_; 
v_es_2508_ = lean_ctor_get(v_x_2505_, 0);
lean_inc_ref(v_es_2508_);
lean_dec_ref(v_x_2505_);
v___x_2509_ = lean_box(2);
v___x_2510_ = ((size_t)5ULL);
v___x_2511_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2512_ = lean_usize_land(v_x_2506_, v___x_2511_);
v_j_2513_ = lean_usize_to_nat(v___x_2512_);
v___x_2514_ = lean_array_get(v___x_2509_, v_es_2508_, v_j_2513_);
lean_dec(v_j_2513_);
lean_dec_ref(v_es_2508_);
switch(lean_obj_tag(v___x_2514_))
{
case 0:
{
lean_object* v_key_2515_; uint8_t v___x_2516_; 
v_key_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_key_2515_);
lean_dec_ref(v___x_2514_);
v___x_2516_ = l_Lean_instBEqMVarId_beq(v_x_2507_, v_key_2515_);
lean_dec(v_key_2515_);
return v___x_2516_;
}
case 1:
{
lean_object* v_node_2517_; size_t v___x_2518_; 
v_node_2517_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_node_2517_);
lean_dec_ref(v___x_2514_);
v___x_2518_ = lean_usize_shift_right(v_x_2506_, v___x_2510_);
v_x_2505_ = v_node_2517_;
v_x_2506_ = v___x_2518_;
goto _start;
}
default: 
{
uint8_t v___x_2520_; 
v___x_2520_ = 0;
return v___x_2520_;
}
}
}
else
{
lean_object* v_ks_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v_ks_2521_ = lean_ctor_get(v_x_2505_, 0);
lean_inc_ref(v_ks_2521_);
lean_dec_ref(v_x_2505_);
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2521_, v___x_2522_, v_x_2507_);
lean_dec_ref(v_ks_2521_);
return v___x_2523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2524_, lean_object* v_x_2525_, lean_object* v_x_2526_){
_start:
{
size_t v_x_2447__boxed_2527_; uint8_t v_res_2528_; lean_object* v_r_2529_; 
v_x_2447__boxed_2527_ = lean_unbox_usize(v_x_2525_);
lean_dec(v_x_2525_);
v_res_2528_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2524_, v_x_2447__boxed_2527_, v_x_2526_);
lean_dec(v_x_2526_);
v_r_2529_ = lean_box(v_res_2528_);
return v_r_2529_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2530_, lean_object* v_x_2531_){
_start:
{
uint64_t v___x_2532_; size_t v___x_2533_; uint8_t v___x_2534_; 
v___x_2532_ = l_Lean_instHashableMVarId_hash(v_x_2531_);
v___x_2533_ = lean_uint64_to_usize(v___x_2532_);
v___x_2534_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2530_, v___x_2533_, v_x_2531_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2535_, lean_object* v_x_2536_){
_start:
{
uint8_t v_res_2537_; lean_object* v_r_2538_; 
v_res_2537_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2535_, v_x_2536_);
lean_dec(v_x_2536_);
v_r_2538_ = lean_box(v_res_2537_);
return v_r_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___x_2542_; lean_object* v_mctx_2543_; lean_object* v_eAssignment_2544_; uint8_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2542_ = lean_st_ref_get(v___y_2540_);
v_mctx_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc_ref(v_mctx_2543_);
lean_dec(v___x_2542_);
v_eAssignment_2544_ = lean_ctor_get(v_mctx_2543_, 7);
lean_inc_ref(v_eAssignment_2544_);
lean_dec_ref(v_mctx_2543_);
v___x_2545_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2544_, v_mvarId_2539_);
v___x_2546_ = lean_box(v___x_2545_);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec(v_mvarId_2548_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2552_, lean_object* v_x_2553_){
_start:
{
if (lean_obj_tag(v_x_2553_) == 0)
{
return v_x_2552_;
}
else
{
lean_object* v_head_2554_; lean_object* v_tail_2555_; lean_object* v___x_2556_; 
v_head_2554_ = lean_ctor_get(v_x_2553_, 0);
lean_inc(v_head_2554_);
v_tail_2555_ = lean_ctor_get(v_x_2553_, 1);
lean_inc(v_tail_2555_);
lean_dec_ref(v_x_2553_);
v___x_2556_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2552_, v_head_2554_);
v_x_2552_ = v___x_2556_;
v_x_2553_ = v_tail_2555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2558_, lean_object* v_a_2559_, uint8_t v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
if (lean_obj_tag(v_a_2561_) == 0)
{
if (lean_obj_tag(v_a_2562_) == 0)
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v_a_2559_);
lean_dec_ref(v_f_2558_);
v___x_2569_ = lean_box(v_a_2560_);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
lean_ctor_set(v___x_2570_, 1, v_a_2563_);
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
else
{
lean_object* v_head_2572_; lean_object* v_tail_2573_; 
v_head_2572_ = lean_ctor_get(v_a_2562_, 0);
lean_inc(v_head_2572_);
v_tail_2573_ = lean_ctor_get(v_a_2562_, 1);
lean_inc(v_tail_2573_);
lean_dec_ref(v_a_2562_);
v_a_2561_ = v_head_2572_;
v_a_2562_ = v_tail_2573_;
goto _start;
}
}
else
{
lean_object* v_head_2575_; lean_object* v_tail_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2619_; 
v_head_2575_ = lean_ctor_get(v_a_2561_, 0);
v_tail_2576_ = lean_ctor_get(v_a_2561_, 1);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_a_2561_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2578_ = v_a_2561_;
v_isShared_2579_ = v_isSharedCheck_2619_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_tail_2576_);
lean_inc(v_head_2575_);
lean_dec(v_a_2561_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2619_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2618_; 
v___x_2580_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2575_, v___y_2565_);
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2618_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2618_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
uint8_t v___x_2585_; 
v___x_2585_ = lean_unbox(v_a_2581_);
lean_dec(v_a_2581_);
if (v___x_2585_ == 0)
{
lean_object* v_zero_2586_; uint8_t v_isZero_2587_; 
v_zero_2586_ = lean_unsigned_to_nat(0u);
v_isZero_2587_ = lean_nat_dec_eq(v_a_2559_, v_zero_2586_);
if (v_isZero_2587_ == 1)
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
lean_del_object(v___x_2578_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v_a_2559_);
lean_dec_ref(v_f_2558_);
v___x_2588_ = lean_array_push(v_a_2563_, v_head_2575_);
v___x_2589_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2588_, v_tail_2576_);
v___x_2590_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2589_, v_a_2562_);
v___x_2591_ = lean_box(v_a_2560_);
v___x_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
lean_ctor_set(v___x_2592_, 1, v___x_2590_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2592_);
v___x_2594_ = v___x_2583_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
else
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_del_object(v___x_2583_);
lean_inc_ref(v_f_2558_);
lean_inc(v_head_2575_);
v___x_2596_ = lean_apply_1(v_f_2558_, v_head_2575_);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
v___x_2597_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7___redArg(v___x_2596_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v_one_2599_; lean_object* v_n_2600_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref(v___x_2597_);
v_one_2599_ = lean_unsigned_to_nat(1u);
v_n_2600_ = lean_nat_sub(v_a_2559_, v_one_2599_);
lean_dec(v_a_2559_);
if (lean_obj_tag(v_a_2598_) == 0)
{
lean_object* v___x_2601_; 
lean_del_object(v___x_2578_);
v___x_2601_ = lean_array_push(v_a_2563_, v_head_2575_);
v_a_2559_ = v_n_2600_;
v_a_2561_ = v_tail_2576_;
v_a_2563_ = v___x_2601_;
goto _start;
}
else
{
lean_object* v_val_2603_; uint8_t v___x_2604_; lean_object* v___x_2606_; 
lean_dec(v_head_2575_);
v_val_2603_ = lean_ctor_get(v_a_2598_, 0);
lean_inc(v_val_2603_);
lean_dec_ref(v_a_2598_);
v___x_2604_ = 1;
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 1, v_a_2562_);
lean_ctor_set(v___x_2578_, 0, v_tail_2576_);
v___x_2606_ = v___x_2578_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_tail_2576_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_a_2562_);
v___x_2606_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
v_a_2559_ = v_n_2600_;
v_a_2560_ = v___x_2604_;
v_a_2561_ = v_val_2603_;
v_a_2562_ = v___x_2606_;
goto _start;
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_del_object(v___x_2578_);
lean_dec(v_tail_2576_);
lean_dec(v_head_2575_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec(v_a_2559_);
lean_dec_ref(v_f_2558_);
v_a_2609_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2597_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2597_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
else
{
lean_del_object(v___x_2583_);
lean_del_object(v___x_2578_);
lean_dec(v_head_2575_);
v_a_2561_ = v_tail_2576_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
uint8_t v_a_2528__boxed_2631_; lean_object* v_res_2632_; 
v_a_2528__boxed_2631_ = lean_unbox(v_a_2622_);
v_res_2632_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2620_, v_a_2621_, v_a_2528__boxed_2631_, v_a_2623_, v_a_2624_, v_a_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2633_, size_t v_i_2634_, size_t v_stop_2635_, lean_object* v_b_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_a_2643_; uint8_t v___x_2647_; 
v___x_2647_ = lean_usize_dec_eq(v_i_2634_, v_stop_2635_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2651_; 
v___x_2648_ = lean_array_uget_borrowed(v_as_2633_, v_i_2634_);
v___x_2651_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2648_, v___y_2638_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; uint8_t v___x_2653_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref(v___x_2651_);
v___x_2653_ = lean_unbox(v_a_2652_);
lean_dec(v_a_2652_);
if (v___x_2653_ == 0)
{
goto v___jp_2649_;
}
else
{
v_a_2643_ = v_b_2636_;
goto v___jp_2642_;
}
}
else
{
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2654_; uint8_t v___x_2655_; 
v_a_2654_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2654_);
lean_dec_ref(v___x_2651_);
v___x_2655_ = lean_unbox(v_a_2654_);
lean_dec(v_a_2654_);
if (v___x_2655_ == 0)
{
v_a_2643_ = v_b_2636_;
goto v___jp_2642_;
}
else
{
goto v___jp_2649_;
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec_ref(v_b_2636_);
v_a_2656_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2651_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2651_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
v___jp_2649_:
{
lean_object* v___x_2650_; 
lean_inc(v___x_2648_);
v___x_2650_ = lean_array_push(v_b_2636_, v___x_2648_);
v_a_2643_ = v___x_2650_;
goto v___jp_2642_;
}
}
else
{
lean_object* v___x_2664_; 
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v_b_2636_);
return v___x_2664_;
}
v___jp_2642_:
{
size_t v___x_2644_; size_t v___x_2645_; 
v___x_2644_ = ((size_t)1ULL);
v___x_2645_ = lean_usize_add(v_i_2634_, v___x_2644_);
v_i_2634_ = v___x_2645_;
v_b_2636_ = v_a_2643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2665_, lean_object* v_i_2666_, lean_object* v_stop_2667_, lean_object* v_b_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
size_t v_i_boxed_2674_; size_t v_stop_boxed_2675_; lean_object* v_res_2676_; 
v_i_boxed_2674_ = lean_unbox_usize(v_i_2666_);
lean_dec(v_i_2666_);
v_stop_boxed_2675_ = lean_unbox_usize(v_stop_2667_);
lean_dec(v_stop_2667_);
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2665_, v_i_boxed_2674_, v_stop_boxed_2675_, v_b_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec_ref(v_as_2665_);
return v_res_2676_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2680_ = lean_array_to_list(v___x_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2681_, lean_object* v_goals_2682_, lean_object* v_maxIters_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2689_ = 0;
v___x_2690_ = lean_box(0);
v___x_2691_ = lean_unsigned_to_nat(0u);
v___x_2692_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
lean_inc(v___y_2687_);
lean_inc_ref(v___y_2686_);
lean_inc(v___y_2685_);
lean_inc_ref(v___y_2684_);
v___x_2693_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2681_, v_maxIters_2683_, v___x_2689_, v_goals_2682_, v___x_2690_, v___x_2692_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2743_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2743_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2743_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v_fst_2698_; lean_object* v_snd_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2742_; 
v_fst_2698_ = lean_ctor_get(v_a_2694_, 0);
v_snd_2699_ = lean_ctor_get(v_a_2694_, 1);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_a_2694_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2701_ = v_a_2694_;
v_isShared_2702_ = v_isSharedCheck_2742_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_snd_2699_);
lean_inc(v_fst_2698_);
lean_dec(v_a_2694_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2742_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v_____do__lift_2704_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2712_ = lean_array_get_size(v_snd_2699_);
v___x_2713_ = lean_nat_dec_lt(v___x_2691_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_del_object(v___x_2701_);
lean_dec(v_snd_2699_);
lean_del_object(v___x_2696_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
v___x_2714_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_fst_2698_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
return v___x_2716_;
}
else
{
uint8_t v___x_2717_; 
v___x_2717_ = lean_nat_dec_le(v___x_2712_, v___x_2712_);
if (v___x_2717_ == 0)
{
if (v___x_2713_ == 0)
{
lean_dec(v_snd_2699_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
v_____do__lift_2704_ = v___x_2692_;
goto v___jp_2703_;
}
else
{
size_t v___x_2718_; size_t v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = ((size_t)0ULL);
v___x_2719_ = lean_usize_of_nat(v___x_2712_);
v___x_2720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2699_, v___x_2718_, v___x_2719_, v___x_2692_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v_snd_2699_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref(v___x_2720_);
v_____do__lift_2704_ = v_a_2721_;
goto v___jp_2703_;
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_del_object(v___x_2701_);
lean_dec(v_fst_2698_);
lean_del_object(v___x_2696_);
v_a_2722_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2720_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2720_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
else
{
size_t v___x_2730_; size_t v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = ((size_t)0ULL);
v___x_2731_ = lean_usize_of_nat(v___x_2712_);
v___x_2732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2699_, v___x_2730_, v___x_2731_, v___x_2692_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v_snd_2699_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref(v___x_2732_);
v_____do__lift_2704_ = v_a_2733_;
goto v___jp_2703_;
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_del_object(v___x_2701_);
lean_dec(v_fst_2698_);
lean_del_object(v___x_2696_);
v_a_2734_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2732_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2732_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
v___jp_2703_:
{
lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2705_ = lean_array_to_list(v_____do__lift_2704_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v___x_2705_);
v___x_2707_ = v___x_2701_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_fst_2698_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2709_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2707_);
v___x_2709_ = v___x_2696_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
v_a_2744_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2693_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2693_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2752_, lean_object* v_goals_2753_, lean_object* v_maxIters_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2752_, v_goals_2753_, v_maxIters_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
return v_res_2760_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2764_, lean_object* v_goals_2765_, lean_object* v_maxIters_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___x_2772_; 
lean_inc(v___y_2770_);
lean_inc_ref(v___y_2769_);
lean_inc(v___y_2768_);
lean_inc_ref(v___y_2767_);
v___x_2772_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2764_, v_goals_2765_, v_maxIters_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2785_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2775_ = v___x_2772_;
v_isShared_2776_ = v_isSharedCheck_2785_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2772_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2785_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v_fst_2777_; uint8_t v___x_2778_; 
v_fst_2777_ = lean_ctor_get(v_a_2773_, 0);
v___x_2778_ = lean_unbox(v_fst_2777_);
if (v___x_2778_ == 1)
{
lean_object* v_snd_2779_; lean_object* v___x_2781_; 
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
v_snd_2779_ = lean_ctor_get(v_a_2773_, 1);
lean_inc(v_snd_2779_);
lean_dec(v_a_2773_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v_snd_2779_);
v___x_2781_ = v___x_2775_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_snd_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_del_object(v___x_2775_);
lean_dec(v_a_2773_);
v___x_2783_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2784_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2783_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
return v___x_2784_;
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
v_a_2786_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2772_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2772_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2794_, lean_object* v_goals_2795_, lean_object* v_maxIters_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2794_, v_goals_2795_, v_maxIters_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2803_, lean_object* v_ctx_2804_, lean_object* v_cfg_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
uint8_t v_backtracking_2812_; 
v_backtracking_2812_ = lean_ctor_get_uint8(v_cfg_2805_, sizeof(void*)*1);
if (v_backtracking_2812_ == 0)
{
lean_object* v_toApplyRulesConfig_2813_; lean_object* v_toBacktrackConfig_2814_; lean_object* v_maxDepth_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_toApplyRulesConfig_2813_ = lean_ctor_get(v_cfg_2805_, 0);
v_toBacktrackConfig_2814_ = lean_ctor_get(v_toApplyRulesConfig_2813_, 0);
v_maxDepth_2815_ = lean_ctor_get(v_toBacktrackConfig_2814_, 0);
lean_inc(v_maxDepth_2815_);
v___x_2816_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2816_, 0, v_cfg_2805_);
lean_closure_set(v___x_2816_, 1, v_lemmas_2803_);
lean_closure_set(v___x_2816_, 2, v_ctx_2804_);
v___x_2817_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2816_, v_a_2806_, v_maxDepth_2815_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
return v___x_2817_;
}
else
{
lean_object* v_toApplyRulesConfig_2818_; lean_object* v_toBacktrackConfig_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_toApplyRulesConfig_2818_ = lean_ctor_get(v_cfg_2805_, 0);
v_toBacktrackConfig_2819_ = lean_ctor_get(v_toApplyRulesConfig_2818_, 0);
lean_inc_ref(v_toBacktrackConfig_2819_);
v___x_2820_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2821_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2821_, 0, v_cfg_2805_);
lean_closure_set(v___x_2821_, 1, v_lemmas_2803_);
lean_closure_set(v___x_2821_, 2, v_ctx_2804_);
v___x_2822_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2819_, v___x_2820_, v___x_2821_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
return v___x_2822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2823_, lean_object* v_ctx_2824_, lean_object* v_cfg_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2823_, v_ctx_2824_, v_cfg_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2833_, v___y_2835_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v_mvarId_2840_);
return v_res_2846_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2847_, lean_object* v_x_2848_, lean_object* v_x_2849_){
_start:
{
uint8_t v___x_2850_; 
v___x_2850_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2848_, v_x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2851_, lean_object* v_x_2852_, lean_object* v_x_2853_){
_start:
{
uint8_t v_res_2854_; lean_object* v_r_2855_; 
v_res_2854_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2851_, v_x_2852_, v_x_2853_);
lean_dec(v_x_2853_);
v_r_2855_ = lean_box(v_res_2854_);
return v_r_2855_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2856_, lean_object* v_x_2857_, size_t v_x_2858_, lean_object* v_x_2859_){
_start:
{
uint8_t v___x_2860_; 
v___x_2860_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2857_, v_x_2858_, v_x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2861_, lean_object* v_x_2862_, lean_object* v_x_2863_, lean_object* v_x_2864_){
_start:
{
size_t v_x_3000__boxed_2865_; uint8_t v_res_2866_; lean_object* v_r_2867_; 
v_x_3000__boxed_2865_ = lean_unbox_usize(v_x_2863_);
lean_dec(v_x_2863_);
v_res_2866_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2861_, v_x_2862_, v_x_3000__boxed_2865_, v_x_2864_);
lean_dec(v_x_2864_);
v_r_2867_ = lean_box(v_res_2866_);
return v_r_2867_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2868_, lean_object* v_keys_2869_, lean_object* v_vals_2870_, lean_object* v_heq_2871_, lean_object* v_i_2872_, lean_object* v_k_2873_){
_start:
{
uint8_t v___x_2874_; 
v___x_2874_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2869_, v_i_2872_, v_k_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2875_, lean_object* v_keys_2876_, lean_object* v_vals_2877_, lean_object* v_heq_2878_, lean_object* v_i_2879_, lean_object* v_k_2880_){
_start:
{
uint8_t v_res_2881_; lean_object* v_r_2882_; 
v_res_2881_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2875_, v_keys_2876_, v_vals_2877_, v_heq_2878_, v_i_2879_, v_k_2880_);
lean_dec(v_k_2880_);
lean_dec_ref(v_vals_2877_);
lean_dec_ref(v_keys_2876_);
v_r_2882_ = lean_box(v_res_2881_);
return v_r_2882_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2885_ = l_Lean_stringToMessageData(v___x_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec_ref(v_x_2894_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2902_, lean_object* v_lemmas_2903_, lean_object* v_ctx_2904_, lean_object* v_goals_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_){
_start:
{
lean_object* v_cfg_2911_; lean_object* v___x_2912_; 
v_cfg_2911_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2902_);
lean_inc(v_a_2909_);
lean_inc_ref(v_a_2908_);
lean_inc(v_a_2907_);
lean_inc_ref(v_a_2906_);
lean_inc(v_goals_2905_);
lean_inc_ref(v_cfg_2911_);
lean_inc_ref(v_ctx_2904_);
lean_inc(v_lemmas_2903_);
v___x_2912_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2903_, v_ctx_2904_, v_cfg_2911_, v_goals_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_dec_ref(v_cfg_2911_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_goals_2905_);
lean_dec_ref(v_ctx_2904_);
lean_dec(v_lemmas_2903_);
return v___x_2912_;
}
else
{
lean_object* v_a_2913_; lean_object* v___f_2914_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; uint8_t v___y_2919_; uint8_t v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v_a_2923_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; uint8_t v___y_2936_; uint8_t v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v_a_2940_; lean_object* v___y_2943_; lean_object* v___y_2944_; uint8_t v___y_2945_; uint8_t v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v_a_2950_; lean_object* v___y_2963_; lean_object* v___y_2964_; uint8_t v___y_2965_; lean_object* v___y_2966_; uint8_t v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v_a_2970_; lean_object* v___y_2973_; lean_object* v___y_2974_; uint8_t v___y_2975_; lean_object* v___y_2976_; uint8_t v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; uint8_t v___y_3015_; uint8_t v___x_3070_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
v___f_2914_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_3070_ = l_Lean_Exception_isInterrupt(v_a_2913_);
if (v___x_3070_ == 0)
{
uint8_t v___x_3071_; 
v___x_3071_ = l_Lean_Exception_isRuntime(v_a_2913_);
v___y_3015_ = v___x_3071_;
goto v___jp_3014_;
}
else
{
lean_dec(v_a_2913_);
v___y_3015_ = v___x_3070_;
goto v___jp_3014_;
}
v___jp_2915_:
{
lean_object* v___x_2924_; double v___x_2925_; double v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2924_ = lean_io_get_num_heartbeats();
v___x_2925_ = lean_float_of_nat(v___y_2918_);
v___x_2926_ = lean_float_of_nat(v___x_2924_);
v___x_2927_ = lean_box_float(v___x_2925_);
v___x_2928_ = lean_box_float(v___x_2926_);
v___x_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2927_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v_a_2923_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___x_2931_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___y_2922_, v___y_2920_, v___y_2917_, v___y_2916_, v___y_2919_, v___y_2921_, v___f_2914_, v___x_2930_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec_ref(v___y_2916_);
return v___x_2931_;
}
v___jp_2932_:
{
lean_object* v___x_2941_; 
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_a_2940_);
v___y_2916_ = v___y_2933_;
v___y_2917_ = v___y_2935_;
v___y_2918_ = v___y_2934_;
v___y_2919_ = v___y_2936_;
v___y_2920_ = v___y_2937_;
v___y_2921_ = v___y_2938_;
v___y_2922_ = v___y_2939_;
v_a_2923_ = v___x_2941_;
goto v___jp_2915_;
}
v___jp_2942_:
{
lean_object* v___x_2951_; double v___x_2952_; double v___x_2953_; double v___x_2954_; double v___x_2955_; double v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2951_ = lean_io_mono_nanos_now();
v___x_2952_ = lean_float_of_nat(v___y_2947_);
v___x_2953_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0);
v___x_2954_ = lean_float_div(v___x_2952_, v___x_2953_);
v___x_2955_ = lean_float_of_nat(v___x_2951_);
v___x_2956_ = lean_float_div(v___x_2955_, v___x_2953_);
v___x_2957_ = lean_box_float(v___x_2954_);
v___x_2958_ = lean_box_float(v___x_2956_);
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2960_, 0, v_a_2950_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___y_2949_, v___y_2946_, v___y_2944_, v___y_2943_, v___y_2945_, v___y_2948_, v___f_2914_, v___x_2960_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec_ref(v___y_2943_);
return v___x_2961_;
}
v___jp_2962_:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v_a_2970_);
v___y_2943_ = v___y_2963_;
v___y_2944_ = v___y_2964_;
v___y_2945_ = v___y_2965_;
v___y_2946_ = v___y_2967_;
v___y_2947_ = v___y_2966_;
v___y_2948_ = v___y_2968_;
v___y_2949_ = v___y_2969_;
v_a_2950_ = v___x_2971_;
goto v___jp_2942_;
}
v___jp_2972_:
{
lean_object* v___x_2980_; lean_object* v_a_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; 
v___x_2980_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg(v_a_2909_);
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref(v___x_2980_);
v___x_2982_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2983_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___y_2973_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_io_mono_nanos_now();
lean_inc(v_a_2909_);
lean_inc_ref(v_a_2908_);
lean_inc(v_a_2907_);
lean_inc_ref(v_a_2906_);
v___x_2985_ = l_Lean_MVarId_exfalso(v___y_2978_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref(v___x_2985_);
v___x_2987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2987_, 0, v_a_2986_);
lean_ctor_set(v___x_2987_, 1, v___y_2976_);
lean_inc(v_a_2909_);
lean_inc_ref(v_a_2908_);
lean_inc(v_a_2907_);
lean_inc_ref(v_a_2906_);
v___x_2988_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2903_, v_ctx_2904_, v_cfg_2911_, v___x_2987_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2988_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2988_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set_tag(v___x_2991_, 1);
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
v___y_2943_ = v___y_2973_;
v___y_2944_ = v___y_2974_;
v___y_2945_ = v___y_2975_;
v___y_2946_ = v___y_2977_;
v___y_2947_ = v___x_2984_;
v___y_2948_ = v_a_2981_;
v___y_2949_ = v___y_2979_;
v_a_2950_ = v___x_2994_;
goto v___jp_2942_;
}
}
}
else
{
lean_object* v_a_2997_; 
v_a_2997_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2997_);
lean_dec_ref(v___x_2988_);
v___y_2963_ = v___y_2973_;
v___y_2964_ = v___y_2974_;
v___y_2965_ = v___y_2975_;
v___y_2966_ = v___x_2984_;
v___y_2967_ = v___y_2977_;
v___y_2968_ = v_a_2981_;
v___y_2969_ = v___y_2979_;
v_a_2970_ = v_a_2997_;
goto v___jp_2962_;
}
}
else
{
lean_object* v_a_2998_; 
lean_dec(v___y_2976_);
lean_dec_ref(v_cfg_2911_);
lean_dec_ref(v_ctx_2904_);
lean_dec(v_lemmas_2903_);
v_a_2998_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2998_);
lean_dec_ref(v___x_2985_);
v___y_2963_ = v___y_2973_;
v___y_2964_ = v___y_2974_;
v___y_2965_ = v___y_2975_;
v___y_2966_ = v___x_2984_;
v___y_2967_ = v___y_2977_;
v___y_2968_ = v_a_2981_;
v___y_2969_ = v___y_2979_;
v_a_2970_ = v_a_2998_;
goto v___jp_2962_;
}
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2909_);
lean_inc_ref(v_a_2908_);
lean_inc(v_a_2907_);
lean_inc_ref(v_a_2906_);
v___x_3000_ = l_Lean_MVarId_exfalso(v___y_2978_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref(v___x_3000_);
v___x_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3002_, 0, v_a_3001_);
lean_ctor_set(v___x_3002_, 1, v___y_2976_);
lean_inc(v_a_2909_);
lean_inc_ref(v_a_2908_);
lean_inc(v_a_2907_);
lean_inc_ref(v_a_2906_);
v___x_3003_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2903_, v_ctx_2904_, v_cfg_2911_, v___x_3002_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_3003_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_3003_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
lean_ctor_set_tag(v___x_3006_, 1);
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
v___y_2916_ = v___y_2973_;
v___y_2917_ = v___y_2974_;
v___y_2918_ = v___x_2999_;
v___y_2919_ = v___y_2975_;
v___y_2920_ = v___y_2977_;
v___y_2921_ = v_a_2981_;
v___y_2922_ = v___y_2979_;
v_a_2923_ = v___x_3009_;
goto v___jp_2915_;
}
}
}
else
{
lean_object* v_a_3012_; 
v_a_3012_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3012_);
lean_dec_ref(v___x_3003_);
v___y_2933_ = v___y_2973_;
v___y_2934_ = v___x_2999_;
v___y_2935_ = v___y_2974_;
v___y_2936_ = v___y_2975_;
v___y_2937_ = v___y_2977_;
v___y_2938_ = v_a_2981_;
v___y_2939_ = v___y_2979_;
v_a_2940_ = v_a_3012_;
goto v___jp_2932_;
}
}
else
{
lean_object* v_a_3013_; 
lean_dec(v___y_2976_);
lean_dec_ref(v_cfg_2911_);
lean_dec_ref(v_ctx_2904_);
lean_dec(v_lemmas_2903_);
v_a_3013_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3013_);
lean_dec_ref(v___x_3000_);
v___y_2933_ = v___y_2973_;
v___y_2934_ = v___x_2999_;
v___y_2935_ = v___y_2974_;
v___y_2936_ = v___y_2975_;
v___y_2937_ = v___y_2977_;
v___y_2938_ = v_a_2981_;
v___y_2939_ = v___y_2979_;
v_a_2940_ = v_a_3013_;
goto v___jp_2932_;
}
}
}
v___jp_3014_:
{
if (v___y_3015_ == 0)
{
if (lean_obj_tag(v_goals_2905_) == 1)
{
lean_object* v_tail_3016_; 
v_tail_3016_ = lean_ctor_get(v_goals_2905_, 1);
lean_inc(v_tail_3016_);
if (lean_obj_tag(v_tail_3016_) == 0)
{
lean_object* v_toApplyRulesConfig_3017_; uint8_t v_exfalso_3018_; 
v_toApplyRulesConfig_3017_ = lean_ctor_get(v_cfg_2911_, 0);
lean_inc_ref(v_toApplyRulesConfig_3017_);
v_exfalso_3018_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3017_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_3017_);
if (v_exfalso_3018_ == 1)
{
lean_object* v_options_3019_; uint8_t v_hasTrace_3020_; 
lean_dec_ref(v___x_2912_);
v_options_3019_ = lean_ctor_get(v_a_2908_, 2);
v_hasTrace_3020_ = lean_ctor_get_uint8(v_options_3019_, sizeof(void*)*1);
if (v_hasTrace_3020_ == 0)
{
lean_object* v_head_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3039_; 
v_head_3021_ = lean_ctor_get(v_goals_2905_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_goals_2905_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; 
v_unused_3040_ = lean_ctor_get(v_goals_2905_, 1);
lean_dec(v_unused_3040_);
v___x_3023_ = v_goals_2905_;
v_isShared_3024_ = v_isSharedCheck_3039_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_head_3021_);
lean_dec(v_goals_2905_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3039_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3025_; 
lean_inc(v_a_2909_);
lean_inc_ref(v_a_2908_);
lean_inc(v_a_2907_);
lean_inc_ref(v_a_2906_);
v___x_3025_ = l_Lean_MVarId_exfalso(v_head_3021_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3028_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref(v___x_3025_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v_a_3026_);
v___x_3028_ = v___x_3023_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3026_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v_tail_3016_);
v___x_3028_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; 
v___x_3029_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2903_, v_ctx_2904_, v_cfg_2911_, v___x_3028_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_3029_;
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_del_object(v___x_3023_);
lean_dec_ref(v_cfg_2911_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_ctx_2904_);
lean_dec(v_lemmas_2903_);
v_a_3031_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3025_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3025_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
else
{
lean_object* v_head_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3068_; 
v_head_3041_ = lean_ctor_get(v_goals_2905_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_goals_2905_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v_goals_2905_, 1);
lean_dec(v_unused_3069_);
v___x_3043_ = v_goals_2905_;
v_isShared_3044_ = v_isSharedCheck_3068_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_head_3041_);
lean_dec(v_goals_2905_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3068_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v_a_3047_; lean_object* v___x_3048_; uint8_t v___x_3049_; 
v___x_3045_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_3046_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg(v___x_3045_, v_a_2908_);
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref(v___x_3046_);
v___x_3048_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_3049_ = lean_unbox(v_a_3047_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = l_Lean_trace_profiler;
v___x_3051_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v_options_3019_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; 
lean_dec(v_a_3047_);
lean_inc(v_a_2909_);
lean_inc_ref(v_a_2908_);
lean_inc(v_a_2907_);
lean_inc_ref(v_a_2906_);
v___x_3052_ = l_Lean_MVarId_exfalso(v_head_3041_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3055_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref(v___x_3052_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v_a_3053_);
v___x_3055_ = v___x_3043_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3053_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v_tail_3016_);
v___x_3055_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3056_; 
v___x_3056_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2903_, v_ctx_2904_, v_cfg_2911_, v___x_3055_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_3056_;
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_del_object(v___x_3043_);
lean_dec_ref(v_cfg_2911_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_ctx_2904_);
lean_dec(v_lemmas_2903_);
v_a_3058_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3052_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3052_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
else
{
uint8_t v___x_3066_; 
lean_del_object(v___x_3043_);
v___x_3066_ = lean_unbox(v_a_3047_);
lean_dec(v_a_3047_);
lean_inc_ref(v_options_3019_);
v___y_2973_ = v_options_3019_;
v___y_2974_ = v___x_3048_;
v___y_2975_ = v___x_3066_;
v___y_2976_ = v_tail_3016_;
v___y_2977_ = v_exfalso_3018_;
v___y_2978_ = v_head_3041_;
v___y_2979_ = v___x_3045_;
goto v___jp_2972_;
}
}
else
{
uint8_t v___x_3067_; 
lean_del_object(v___x_3043_);
v___x_3067_ = lean_unbox(v_a_3047_);
lean_dec(v_a_3047_);
lean_inc_ref(v_options_3019_);
v___y_2973_ = v_options_3019_;
v___y_2974_ = v___x_3048_;
v___y_2975_ = v___x_3067_;
v___y_2976_ = v_tail_3016_;
v___y_2977_ = v_exfalso_3018_;
v___y_2978_ = v_head_3041_;
v___y_2979_ = v___x_3045_;
goto v___jp_2972_;
}
}
}
}
else
{
lean_dec_ref(v_goals_2905_);
lean_dec_ref(v_cfg_2911_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_ctx_2904_);
lean_dec(v_lemmas_2903_);
return v___x_2912_;
}
}
else
{
lean_dec_ref(v_goals_2905_);
lean_dec(v_tail_3016_);
lean_dec_ref(v_cfg_2911_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_ctx_2904_);
lean_dec(v_lemmas_2903_);
return v___x_2912_;
}
}
else
{
lean_dec_ref(v_cfg_2911_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_goals_2905_);
lean_dec_ref(v_ctx_2904_);
lean_dec(v_lemmas_2903_);
return v___x_2912_;
}
}
else
{
lean_dec_ref(v_cfg_2911_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_goals_2905_);
lean_dec_ref(v_ctx_2904_);
lean_dec(v_lemmas_2903_);
return v___x_2912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_3072_, lean_object* v_lemmas_3073_, lean_object* v_ctx_3074_, lean_object* v_goals_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_3072_, v_lemmas_3073_, v_ctx_3074_, v_goals_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_3082_, lean_object* v_x_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
if (lean_obj_tag(v_x_3082_) == 0)
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
v___x_3089_ = l_List_reverse___redArg(v_x_3083_);
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
return v___x_3090_;
}
else
{
lean_object* v_head_3091_; lean_object* v_tail_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3115_; 
v_head_3091_ = lean_ctor_get(v_x_3082_, 0);
v_tail_3092_ = lean_ctor_get(v_x_3082_, 1);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_x_3082_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3094_ = v_x_3082_;
v_isShared_3095_ = v_isSharedCheck_3115_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_tail_3092_);
lean_inc(v_head_3091_);
lean_dec(v_x_3082_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3115_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; 
lean_inc(v___y_3087_);
lean_inc_ref(v___y_3086_);
lean_inc(v___y_3085_);
lean_inc_ref(v___y_3084_);
v___x_3096_ = l_Lean_Expr_applySymm(v_head_3091_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
lean_dec_ref(v___x_3096_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 1, v_x_3083_);
lean_ctor_set(v___x_3094_, 0, v_a_3097_);
v___x_3099_ = v___x_3094_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3097_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_x_3083_);
v___x_3099_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
v_x_3082_ = v_tail_3092_;
v_x_3083_ = v___x_3099_;
goto _start;
}
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3114_; 
lean_del_object(v___x_3094_);
v_a_3102_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3104_ = v___x_3096_;
v_isShared_3105_ = v_isSharedCheck_3114_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3096_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3114_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
uint8_t v___y_3107_; uint8_t v___x_3112_; 
v___x_3112_ = l_Lean_Exception_isInterrupt(v_a_3102_);
if (v___x_3112_ == 0)
{
uint8_t v___x_3113_; 
lean_inc(v_a_3102_);
v___x_3113_ = l_Lean_Exception_isRuntime(v_a_3102_);
v___y_3107_ = v___x_3113_;
goto v___jp_3106_;
}
else
{
v___y_3107_ = v___x_3112_;
goto v___jp_3106_;
}
v___jp_3106_:
{
if (v___y_3107_ == 0)
{
lean_del_object(v___x_3104_);
lean_dec(v_a_3102_);
v_x_3082_ = v_tail_3092_;
goto _start;
}
else
{
lean_object* v___x_3110_; 
lean_dec(v_tail_3092_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v_x_3083_);
if (v_isShared_3105_ == 0)
{
v___x_3110_ = v___x_3104_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3102_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_3116_, lean_object* v_x_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_3116_, v_x_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_3124_, lean_object* v_hyps_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_){
_start:
{
if (v_symm_3124_ == 0)
{
lean_object* v___x_3131_; 
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v_hyps_3125_);
return v___x_3131_;
}
else
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = lean_box(0);
lean_inc(v_hyps_3125_);
v___x_3133_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_3125_, v___x_3132_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3142_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3136_ = v___x_3133_;
v_isShared_3137_ = v_isSharedCheck_3142_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3142_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3138_; lean_object* v___x_3140_; 
v___x_3138_ = l_List_appendTR___redArg(v_hyps_3125_, v_a_3134_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v___x_3138_);
v___x_3140_ = v___x_3136_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3138_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
else
{
lean_dec(v_hyps_3125_);
return v___x_3133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3143_, lean_object* v_hyps_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_){
_start:
{
uint8_t v_symm_boxed_3150_; lean_object* v_res_3151_; 
v_symm_boxed_3150_ = lean_unbox(v_symm_3143_);
v_res_3151_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3150_, v_hyps_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3152_, size_t v_sz_3153_, size_t v_i_3154_, lean_object* v_b_3155_){
_start:
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_usize_dec_lt(v_i_3154_, v_sz_3153_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; 
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v_b_3155_);
return v___x_3158_;
}
else
{
lean_object* v_snd_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3177_; 
v_snd_3159_ = lean_ctor_get(v_b_3155_, 1);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_b_3155_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; 
v_unused_3178_ = lean_ctor_get(v_b_3155_, 0);
lean_dec(v_unused_3178_);
v___x_3161_ = v_b_3155_;
v_isShared_3162_ = v_isSharedCheck_3177_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_snd_3159_);
lean_dec(v_b_3155_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3177_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v_a_3165_; lean_object* v_a_3172_; 
v___x_3163_ = lean_box(0);
v_a_3172_ = lean_array_uget_borrowed(v_as_3152_, v_i_3154_);
if (lean_obj_tag(v_a_3172_) == 0)
{
v_a_3165_ = v_snd_3159_;
goto v___jp_3164_;
}
else
{
lean_object* v_val_3173_; uint8_t v___x_3174_; 
v_val_3173_ = lean_ctor_get(v_a_3172_, 0);
v___x_3174_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3173_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_inc(v_val_3173_);
v___x_3175_ = l_Lean_LocalDecl_toExpr(v_val_3173_);
v___x_3176_ = lean_array_push(v_snd_3159_, v___x_3175_);
v_a_3165_ = v___x_3176_;
goto v___jp_3164_;
}
else
{
v_a_3165_ = v_snd_3159_;
goto v___jp_3164_;
}
}
v___jp_3164_:
{
lean_object* v___x_3167_; 
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 1, v_a_3165_);
lean_ctor_set(v___x_3161_, 0, v___x_3163_);
v___x_3167_ = v___x_3161_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_a_3165_);
v___x_3167_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
size_t v___x_3168_; size_t v___x_3169_; 
v___x_3168_ = ((size_t)1ULL);
v___x_3169_ = lean_usize_add(v_i_3154_, v___x_3168_);
v_i_3154_ = v___x_3169_;
v_b_3155_ = v___x_3167_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3179_, lean_object* v_sz_3180_, lean_object* v_i_3181_, lean_object* v_b_3182_, lean_object* v___y_3183_){
_start:
{
size_t v_sz_boxed_3184_; size_t v_i_boxed_3185_; lean_object* v_res_3186_; 
v_sz_boxed_3184_ = lean_unbox_usize(v_sz_3180_);
lean_dec(v_sz_3180_);
v_i_boxed_3185_ = lean_unbox_usize(v_i_3181_);
lean_dec(v_i_3181_);
v_res_3186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3179_, v_sz_boxed_3184_, v_i_boxed_3185_, v_b_3182_);
lean_dec_ref(v_as_3179_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3187_, size_t v_sz_3188_, size_t v_i_3189_, lean_object* v_b_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
uint8_t v___x_3198_; 
v___x_3198_ = lean_usize_dec_lt(v_i_3189_, v_sz_3188_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; 
v___x_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3199_, 0, v_b_3190_);
return v___x_3199_;
}
else
{
lean_object* v_snd_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3218_; 
v_snd_3200_ = lean_ctor_get(v_b_3190_, 1);
v_isSharedCheck_3218_ = !lean_is_exclusive(v_b_3190_);
if (v_isSharedCheck_3218_ == 0)
{
lean_object* v_unused_3219_; 
v_unused_3219_ = lean_ctor_get(v_b_3190_, 0);
lean_dec(v_unused_3219_);
v___x_3202_ = v_b_3190_;
v_isShared_3203_ = v_isSharedCheck_3218_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_snd_3200_);
lean_dec(v_b_3190_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3218_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v_a_3206_; lean_object* v_a_3213_; 
v___x_3204_ = lean_box(0);
v_a_3213_ = lean_array_uget_borrowed(v_as_3187_, v_i_3189_);
if (lean_obj_tag(v_a_3213_) == 0)
{
v_a_3206_ = v_snd_3200_;
goto v___jp_3205_;
}
else
{
lean_object* v_val_3214_; uint8_t v___x_3215_; 
v_val_3214_ = lean_ctor_get(v_a_3213_, 0);
v___x_3215_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3214_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_inc(v_val_3214_);
v___x_3216_ = l_Lean_LocalDecl_toExpr(v_val_3214_);
v___x_3217_ = lean_array_push(v_snd_3200_, v___x_3216_);
v_a_3206_ = v___x_3217_;
goto v___jp_3205_;
}
else
{
v_a_3206_ = v_snd_3200_;
goto v___jp_3205_;
}
}
v___jp_3205_:
{
lean_object* v___x_3208_; 
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 1, v_a_3206_);
lean_ctor_set(v___x_3202_, 0, v___x_3204_);
v___x_3208_ = v___x_3202_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v_a_3206_);
v___x_3208_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
size_t v___x_3209_; size_t v___x_3210_; lean_object* v___x_3211_; 
v___x_3209_ = ((size_t)1ULL);
v___x_3210_ = lean_usize_add(v_i_3189_, v___x_3209_);
v___x_3211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3187_, v_sz_3188_, v___x_3210_, v___x_3208_);
return v___x_3211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3220_, lean_object* v_sz_3221_, lean_object* v_i_3222_, lean_object* v_b_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
size_t v_sz_boxed_3231_; size_t v_i_boxed_3232_; lean_object* v_res_3233_; 
v_sz_boxed_3231_ = lean_unbox_usize(v_sz_3221_);
lean_dec(v_sz_3221_);
v_i_boxed_3232_ = lean_unbox_usize(v_i_3222_);
lean_dec(v_i_3222_);
v_res_3233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3220_, v_sz_boxed_3231_, v_i_boxed_3232_, v_b_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec_ref(v_as_3220_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3234_, size_t v_sz_3235_, size_t v_i_3236_, lean_object* v_b_3237_){
_start:
{
uint8_t v___x_3239_; 
v___x_3239_ = lean_usize_dec_lt(v_i_3236_, v_sz_3235_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; 
v___x_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3240_, 0, v_b_3237_);
return v___x_3240_;
}
else
{
lean_object* v_snd_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3259_; 
v_snd_3241_ = lean_ctor_get(v_b_3237_, 1);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_b_3237_);
if (v_isSharedCheck_3259_ == 0)
{
lean_object* v_unused_3260_; 
v_unused_3260_ = lean_ctor_get(v_b_3237_, 0);
lean_dec(v_unused_3260_);
v___x_3243_ = v_b_3237_;
v_isShared_3244_ = v_isSharedCheck_3259_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_snd_3241_);
lean_dec(v_b_3237_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3259_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3245_; lean_object* v_a_3247_; lean_object* v_a_3254_; 
v___x_3245_ = lean_box(0);
v_a_3254_ = lean_array_uget_borrowed(v_as_3234_, v_i_3236_);
if (lean_obj_tag(v_a_3254_) == 0)
{
v_a_3247_ = v_snd_3241_;
goto v___jp_3246_;
}
else
{
lean_object* v_val_3255_; uint8_t v___x_3256_; 
v_val_3255_ = lean_ctor_get(v_a_3254_, 0);
v___x_3256_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3255_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
lean_inc(v_val_3255_);
v___x_3257_ = l_Lean_LocalDecl_toExpr(v_val_3255_);
v___x_3258_ = lean_array_push(v_snd_3241_, v___x_3257_);
v_a_3247_ = v___x_3258_;
goto v___jp_3246_;
}
else
{
v_a_3247_ = v_snd_3241_;
goto v___jp_3246_;
}
}
v___jp_3246_:
{
lean_object* v___x_3249_; 
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 1, v_a_3247_);
lean_ctor_set(v___x_3243_, 0, v___x_3245_);
v___x_3249_ = v___x_3243_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v_a_3247_);
v___x_3249_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
size_t v___x_3250_; size_t v___x_3251_; 
v___x_3250_ = ((size_t)1ULL);
v___x_3251_ = lean_usize_add(v_i_3236_, v___x_3250_);
v_i_3236_ = v___x_3251_;
v_b_3237_ = v___x_3249_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3261_, lean_object* v_sz_3262_, lean_object* v_i_3263_, lean_object* v_b_3264_, lean_object* v___y_3265_){
_start:
{
size_t v_sz_boxed_3266_; size_t v_i_boxed_3267_; lean_object* v_res_3268_; 
v_sz_boxed_3266_ = lean_unbox_usize(v_sz_3262_);
lean_dec(v_sz_3262_);
v_i_boxed_3267_ = lean_unbox_usize(v_i_3263_);
lean_dec(v_i_3263_);
v_res_3268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3261_, v_sz_boxed_3266_, v_i_boxed_3267_, v_b_3264_);
lean_dec_ref(v_as_3261_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3269_, size_t v_sz_3270_, size_t v_i_3271_, lean_object* v_b_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
uint8_t v___x_3280_; 
v___x_3280_ = lean_usize_dec_lt(v_i_3271_, v_sz_3270_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_b_3272_);
return v___x_3281_;
}
else
{
lean_object* v_snd_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3300_; 
v_snd_3282_ = lean_ctor_get(v_b_3272_, 1);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_b_3272_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; 
v_unused_3301_ = lean_ctor_get(v_b_3272_, 0);
lean_dec(v_unused_3301_);
v___x_3284_ = v_b_3272_;
v_isShared_3285_ = v_isSharedCheck_3300_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_snd_3282_);
lean_dec(v_b_3272_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3300_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v_a_3288_; lean_object* v_a_3295_; 
v___x_3286_ = lean_box(0);
v_a_3295_ = lean_array_uget_borrowed(v_as_3269_, v_i_3271_);
if (lean_obj_tag(v_a_3295_) == 0)
{
v_a_3288_ = v_snd_3282_;
goto v___jp_3287_;
}
else
{
lean_object* v_val_3296_; uint8_t v___x_3297_; 
v_val_3296_ = lean_ctor_get(v_a_3295_, 0);
v___x_3297_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3296_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_inc(v_val_3296_);
v___x_3298_ = l_Lean_LocalDecl_toExpr(v_val_3296_);
v___x_3299_ = lean_array_push(v_snd_3282_, v___x_3298_);
v_a_3288_ = v___x_3299_;
goto v___jp_3287_;
}
else
{
v_a_3288_ = v_snd_3282_;
goto v___jp_3287_;
}
}
v___jp_3287_:
{
lean_object* v___x_3290_; 
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v_a_3288_);
lean_ctor_set(v___x_3284_, 0, v___x_3286_);
v___x_3290_ = v___x_3284_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3286_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_a_3288_);
v___x_3290_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
size_t v___x_3291_; size_t v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = ((size_t)1ULL);
v___x_3292_ = lean_usize_add(v_i_3271_, v___x_3291_);
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3269_, v_sz_3270_, v___x_3292_, v___x_3290_);
return v___x_3293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3302_, lean_object* v_sz_3303_, lean_object* v_i_3304_, lean_object* v_b_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
size_t v_sz_boxed_3313_; size_t v_i_boxed_3314_; lean_object* v_res_3315_; 
v_sz_boxed_3313_ = lean_unbox_usize(v_sz_3303_);
lean_dec(v_sz_3303_);
v_i_boxed_3314_ = lean_unbox_usize(v_i_3304_);
lean_dec(v_i_3304_);
v_res_3315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3302_, v_sz_boxed_3313_, v_i_boxed_3314_, v_b_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec_ref(v_as_3302_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_inh_3316_, lean_object* v_n_3317_, lean_object* v_b_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
if (lean_obj_tag(v_n_3317_) == 0)
{
lean_object* v_cs_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3360_; 
v_cs_3326_ = lean_ctor_get(v_n_3317_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v_n_3317_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3328_ = v_n_3317_;
v_isShared_3329_ = v_isSharedCheck_3360_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_cs_3326_);
lean_dec(v_n_3317_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3360_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; size_t v_sz_3332_; size_t v___x_3333_; lean_object* v___x_3334_; 
v___x_3330_ = lean_box(0);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
lean_ctor_set(v___x_3331_, 1, v_b_3318_);
v_sz_3332_ = lean_array_size(v_cs_3326_);
v___x_3333_ = ((size_t)0ULL);
v___x_3334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_inh_3316_, v_cs_3326_, v_sz_3332_, v___x_3333_, v___x_3331_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec_ref(v_cs_3326_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3351_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3351_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3351_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_fst_3339_; 
v_fst_3339_ = lean_ctor_get(v_a_3335_, 0);
if (lean_obj_tag(v_fst_3339_) == 0)
{
lean_object* v_snd_3340_; lean_object* v___x_3342_; 
v_snd_3340_ = lean_ctor_get(v_a_3335_, 1);
lean_inc(v_snd_3340_);
lean_dec(v_a_3335_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set_tag(v___x_3328_, 1);
lean_ctor_set(v___x_3328_, 0, v_snd_3340_);
v___x_3342_ = v___x_3328_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_snd_3340_);
v___x_3342_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3344_; 
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3342_);
v___x_3344_ = v___x_3337_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
else
{
lean_object* v_val_3347_; lean_object* v___x_3349_; 
lean_inc_ref(v_fst_3339_);
lean_dec(v_a_3335_);
lean_del_object(v___x_3328_);
v_val_3347_ = lean_ctor_get(v_fst_3339_, 0);
lean_inc(v_val_3347_);
lean_dec_ref(v_fst_3339_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v_val_3347_);
v___x_3349_ = v___x_3337_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_val_3347_);
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
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_del_object(v___x_3328_);
v_a_3352_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3334_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3334_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
}
else
{
lean_object* v_vs_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3395_; 
v_vs_3361_ = lean_ctor_get(v_n_3317_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_n_3317_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3363_ = v_n_3317_;
v_isShared_3364_ = v_isSharedCheck_3395_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_vs_3361_);
lean_dec(v_n_3317_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3395_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; size_t v_sz_3367_; size_t v___x_3368_; lean_object* v___x_3369_; 
v___x_3365_ = lean_box(0);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v_b_3318_);
v_sz_3367_ = lean_array_size(v_vs_3361_);
v___x_3368_ = ((size_t)0ULL);
v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3361_, v_sz_3367_, v___x_3368_, v___x_3366_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec_ref(v_vs_3361_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3386_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3372_ = v___x_3369_;
v_isShared_3373_ = v_isSharedCheck_3386_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3369_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3386_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v_fst_3374_; 
v_fst_3374_ = lean_ctor_get(v_a_3370_, 0);
if (lean_obj_tag(v_fst_3374_) == 0)
{
lean_object* v_snd_3375_; lean_object* v___x_3377_; 
v_snd_3375_ = lean_ctor_get(v_a_3370_, 1);
lean_inc(v_snd_3375_);
lean_dec(v_a_3370_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v_snd_3375_);
v___x_3377_ = v___x_3363_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_snd_3375_);
v___x_3377_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3377_);
v___x_3379_ = v___x_3372_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
else
{
lean_object* v_val_3382_; lean_object* v___x_3384_; 
lean_inc_ref(v_fst_3374_);
lean_dec(v_a_3370_);
lean_del_object(v___x_3363_);
v_val_3382_ = lean_ctor_get(v_fst_3374_, 0);
lean_inc(v_val_3382_);
lean_dec_ref(v_fst_3374_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v_val_3382_);
v___x_3384_ = v___x_3372_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_val_3382_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_del_object(v___x_3363_);
v_a_3387_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3369_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3369_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_inh_3396_, lean_object* v_as_3397_, size_t v_sz_3398_, size_t v_i_3399_, lean_object* v_b_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
uint8_t v___x_3408_; 
v___x_3408_ = lean_usize_dec_lt(v_i_3399_, v_sz_3398_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; 
v___x_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3409_, 0, v_b_3400_);
return v___x_3409_;
}
else
{
lean_object* v_snd_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3444_; 
v_snd_3410_ = lean_ctor_get(v_b_3400_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_b_3400_);
if (v_isSharedCheck_3444_ == 0)
{
lean_object* v_unused_3445_; 
v_unused_3445_ = lean_ctor_get(v_b_3400_, 0);
lean_dec(v_unused_3445_);
v___x_3412_ = v_b_3400_;
v_isShared_3413_ = v_isSharedCheck_3444_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_snd_3410_);
lean_dec(v_b_3400_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3444_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v_a_3414_; lean_object* v___x_3415_; 
v_a_3414_ = lean_array_uget_borrowed(v_as_3397_, v_i_3399_);
lean_inc(v_snd_3410_);
lean_inc(v_a_3414_);
v___x_3415_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_inh_3396_, v_a_3414_, v_snd_3410_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3435_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3435_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3435_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
if (lean_obj_tag(v_a_3416_) == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3420_, 0, v_a_3416_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v___x_3420_);
v___x_3422_ = v___x_3412_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_snd_3410_);
v___x_3422_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3424_; 
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3422_);
v___x_3424_ = v___x_3418_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3428_; lean_object* v___x_3430_; 
lean_del_object(v___x_3418_);
lean_dec(v_snd_3410_);
v_a_3427_ = lean_ctor_get(v_a_3416_, 0);
lean_inc(v_a_3427_);
lean_dec_ref(v_a_3416_);
v___x_3428_ = lean_box(0);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 1, v_a_3427_);
lean_ctor_set(v___x_3412_, 0, v___x_3428_);
v___x_3430_ = v___x_3412_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3428_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_a_3427_);
v___x_3430_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
size_t v___x_3431_; size_t v___x_3432_; 
v___x_3431_ = ((size_t)1ULL);
v___x_3432_ = lean_usize_add(v_i_3399_, v___x_3431_);
v_i_3399_ = v___x_3432_;
v_b_3400_ = v___x_3430_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_del_object(v___x_3412_);
lean_dec(v_snd_3410_);
v_a_3436_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3415_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3415_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_inh_3446_, lean_object* v_as_3447_, lean_object* v_sz_3448_, lean_object* v_i_3449_, lean_object* v_b_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
size_t v_sz_boxed_3458_; size_t v_i_boxed_3459_; lean_object* v_res_3460_; 
v_sz_boxed_3458_ = lean_unbox_usize(v_sz_3448_);
lean_dec(v_sz_3448_);
v_i_boxed_3459_ = lean_unbox_usize(v_i_3449_);
lean_dec(v_i_3449_);
v_res_3460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_inh_3446_, v_as_3447_, v_sz_boxed_3458_, v_i_boxed_3459_, v_b_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec_ref(v_as_3447_);
lean_dec_ref(v_inh_3446_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_inh_3461_, lean_object* v_n_3462_, lean_object* v_b_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_inh_3461_, v_n_3462_, v_b_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec_ref(v_inh_3461_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3472_, lean_object* v_init_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v_root_3481_; lean_object* v_tail_3482_; lean_object* v___x_3483_; 
v_root_3481_ = lean_ctor_get(v_t_3472_, 0);
lean_inc_ref(v_root_3481_);
v_tail_3482_ = lean_ctor_get(v_t_3472_, 1);
lean_inc_ref(v_tail_3482_);
lean_dec_ref(v_t_3472_);
lean_inc_ref(v_init_3473_);
v___x_3483_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3473_, v_root_3481_, v_init_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec_ref(v_init_3473_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3520_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3486_ = v___x_3483_;
v_isShared_3487_ = v_isSharedCheck_3520_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3483_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3520_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
if (lean_obj_tag(v_a_3484_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3490_; 
lean_dec_ref(v_tail_3482_);
v_a_3488_ = lean_ctor_get(v_a_3484_, 0);
lean_inc(v_a_3488_);
lean_dec_ref(v_a_3484_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v_a_3488_);
v___x_3490_ = v___x_3486_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; size_t v_sz_3495_; size_t v___x_3496_; lean_object* v___x_3497_; 
lean_del_object(v___x_3486_);
v_a_3492_ = lean_ctor_get(v_a_3484_, 0);
lean_inc(v_a_3492_);
lean_dec_ref(v_a_3484_);
v___x_3493_ = lean_box(0);
v___x_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v_a_3492_);
v_sz_3495_ = lean_array_size(v_tail_3482_);
v___x_3496_ = ((size_t)0ULL);
v___x_3497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3482_, v_sz_3495_, v___x_3496_, v___x_3494_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec_ref(v_tail_3482_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3511_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3511_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3511_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v_fst_3502_; 
v_fst_3502_ = lean_ctor_get(v_a_3498_, 0);
if (lean_obj_tag(v_fst_3502_) == 0)
{
lean_object* v_snd_3503_; lean_object* v___x_3505_; 
v_snd_3503_ = lean_ctor_get(v_a_3498_, 1);
lean_inc(v_snd_3503_);
lean_dec(v_a_3498_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v_snd_3503_);
v___x_3505_ = v___x_3500_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_snd_3503_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
else
{
lean_object* v_val_3507_; lean_object* v___x_3509_; 
lean_inc_ref(v_fst_3502_);
lean_dec(v_a_3498_);
v_val_3507_ = lean_ctor_get(v_fst_3502_, 0);
lean_inc(v_val_3507_);
lean_dec_ref(v_fst_3502_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v_val_3507_);
v___x_3509_ = v___x_3500_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_val_3507_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
v_a_3512_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3497_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3497_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
}
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec_ref(v_tail_3482_);
v_a_3521_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3483_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3483_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3529_, lean_object* v_init_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3529_, v_init_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_lctx_3548_; lean_object* v_decls_3549_; lean_object* v_hs_3550_; lean_object* v___x_3551_; 
v_lctx_3548_ = lean_ctor_get(v___y_3543_, 2);
v_decls_3549_ = lean_ctor_get(v_lctx_3548_, 1);
lean_inc_ref(v_decls_3549_);
v_hs_3550_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3551_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3549_, v_hs_3550_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
lean_dec_ref(v___y_3543_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3560_, lean_object* v_cfg_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
if (v_only_3560_ == 0)
{
lean_object* v___x_3569_; 
lean_inc_ref(v___y_3564_);
v___x_3569_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_toApplyRulesConfig_3570_; lean_object* v_a_3571_; uint8_t v_symm_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v_toApplyRulesConfig_3570_ = lean_ctor_get(v_cfg_3561_, 0);
v_a_3571_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3571_);
lean_dec_ref(v___x_3569_);
v_symm_3572_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3570_, sizeof(void*)*2 + 1);
v___x_3573_ = lean_array_to_list(v_a_3571_);
v___x_3574_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3572_, v___x_3573_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
return v___x_3574_;
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
v_a_3575_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3569_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3569_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
v___x_3583_ = lean_box(0);
v___x_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
return v___x_3584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3585_, lean_object* v_cfg_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
uint8_t v_only_boxed_3594_; lean_object* v_res_3595_; 
v_only_boxed_3594_ = lean_unbox(v_only_3585_);
v_res_3595_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3594_, v_cfg_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v_cfg_3586_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3596_, lean_object* v_lemmas_3597_, uint8_t v_only_3598_, lean_object* v_g_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_toApplyRulesConfig_3605_; uint8_t v_intro_3606_; uint8_t v_constructor_3607_; uint8_t v_suggestions_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3621_; 
v_toApplyRulesConfig_3605_ = lean_ctor_get(v_cfg_3596_, 0);
v_intro_3606_ = lean_ctor_get_uint8(v_cfg_3596_, sizeof(void*)*1 + 1);
v_constructor_3607_ = lean_ctor_get_uint8(v_cfg_3596_, sizeof(void*)*1 + 2);
v_suggestions_3608_ = lean_ctor_get_uint8(v_cfg_3596_, sizeof(void*)*1 + 3);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_cfg_3596_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3610_ = v_cfg_3596_;
v_isShared_3611_ = v_isSharedCheck_3621_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_toApplyRulesConfig_3605_);
lean_dec(v_cfg_3596_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3621_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; lean_object* v_ctx_3613_; uint8_t v___x_3614_; lean_object* v___x_3616_; 
v___x_3612_ = lean_box(v_only_3598_);
v_ctx_3613_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3613_, 0, v___x_3612_);
v___x_3614_ = 0;
if (v_isShared_3611_ == 0)
{
v___x_3616_ = v___x_3610_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_toApplyRulesConfig_3605_);
lean_ctor_set_uint8(v_reuseFailAlloc_3620_, sizeof(void*)*1 + 1, v_intro_3606_);
lean_ctor_set_uint8(v_reuseFailAlloc_3620_, sizeof(void*)*1 + 2, v_constructor_3607_);
lean_ctor_set_uint8(v_reuseFailAlloc_3620_, sizeof(void*)*1 + 3, v_suggestions_3608_);
v___x_3616_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
lean_ctor_set_uint8(v___x_3616_, sizeof(void*)*1, v___x_3614_);
v___x_3617_ = lean_box(0);
v___x_3618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3618_, 0, v_g_3599_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3616_, v_lemmas_3597_, v_ctx_3613_, v___x_3618_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
return v___x_3619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3622_, lean_object* v_lemmas_3623_, lean_object* v_only_3624_, lean_object* v_g_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_){
_start:
{
uint8_t v_only_boxed_3631_; lean_object* v_res_3632_; 
v_only_boxed_3631_ = lean_unbox(v_only_3624_);
v_res_3632_ = l_Lean_MVarId_applyRules(v_cfg_3622_, v_lemmas_3623_, v_only_boxed_3631_, v_g_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3633_, size_t v_sz_3634_, size_t v_i_3635_, lean_object* v_b_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3633_, v_sz_3634_, v_i_3635_, v_b_3636_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3645_, lean_object* v_sz_3646_, lean_object* v_i_3647_, lean_object* v_b_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
size_t v_sz_boxed_3656_; size_t v_i_boxed_3657_; lean_object* v_res_3658_; 
v_sz_boxed_3656_ = lean_unbox_usize(v_sz_3646_);
lean_dec(v_sz_3646_);
v_i_boxed_3657_ = lean_unbox_usize(v_i_3647_);
lean_dec(v_i_3647_);
v_res_3658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3645_, v_sz_boxed_3656_, v_i_boxed_3657_, v_b_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec_ref(v_as_3645_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3659_, size_t v_sz_3660_, size_t v_i_3661_, lean_object* v_b_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3659_, v_sz_3660_, v_i_3661_, v_b_3662_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3671_, lean_object* v_sz_3672_, lean_object* v_i_3673_, lean_object* v_b_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
size_t v_sz_boxed_3682_; size_t v_i_boxed_3683_; lean_object* v_res_3684_; 
v_sz_boxed_3682_ = lean_unbox_usize(v_sz_3672_);
lean_dec(v_sz_3672_);
v_i_boxed_3683_ = lean_unbox_usize(v_i_3673_);
lean_dec(v_i_3673_);
v_res_3684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3671_, v_sz_boxed_3682_, v_i_boxed_3683_, v_b_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v_as_3671_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v___x_3693_; uint8_t v___x_3694_; lean_object* v___x_3695_; 
v___x_3693_ = lean_box(0);
v___x_3694_ = 1;
v___x_3695_ = l_Lean_Elab_Term_elabTerm(v_t_3685_, v___x_3693_, v___x_3694_, v___x_3694_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v_ref_3710_; uint8_t v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v_ref_3710_ = lean_ctor_get(v___y_3707_, 5);
v___x_3711_ = 0;
v___x_3712_ = l_Lean_SourceInfo_fromRef(v_ref_3710_, v___x_3711_);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
return v_res_3719_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3720_, lean_object* v_x_3721_){
_start:
{
if (lean_obj_tag(v_x_3721_) == 0)
{
uint8_t v___x_3722_; 
v___x_3722_ = 0;
return v___x_3722_;
}
else
{
lean_object* v_head_3723_; lean_object* v_tail_3724_; uint8_t v___x_3725_; 
v_head_3723_ = lean_ctor_get(v_x_3721_, 0);
v_tail_3724_ = lean_ctor_get(v_x_3721_, 1);
v___x_3725_ = lean_expr_eqv(v_a_3720_, v_head_3723_);
if (v___x_3725_ == 0)
{
v_x_3721_ = v_tail_3724_;
goto _start;
}
else
{
return v___x_3725_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3727_, lean_object* v_x_3728_){
_start:
{
uint8_t v_res_3729_; lean_object* v_r_3730_; 
v_res_3729_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3727_, v_x_3728_);
lean_dec(v_x_3728_);
lean_dec_ref(v_a_3727_);
v_r_3730_ = lean_box(v_res_3729_);
return v_r_3730_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3731_, lean_object* v_x_3732_){
_start:
{
uint8_t v___x_3733_; 
v___x_3733_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3732_, v_ys_3731_);
if (v___x_3733_ == 0)
{
uint8_t v___x_3734_; 
v___x_3734_ = 1;
return v___x_3734_;
}
else
{
uint8_t v___x_3735_; 
v___x_3735_ = 0;
return v___x_3735_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3736_, lean_object* v_x_3737_){
_start:
{
uint8_t v_res_3738_; lean_object* v_r_3739_; 
v_res_3738_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3736_, v_x_3737_);
lean_dec_ref(v_x_3737_);
lean_dec(v_ys_3736_);
v_r_3739_ = lean_box(v_res_3738_);
return v_r_3739_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3740_, lean_object* v_ys_3741_){
_start:
{
lean_object* v___f_3742_; lean_object* v___x_3743_; 
v___f_3742_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3742_, 0, v_ys_3741_);
v___x_3743_ = l_List_filter___redArg(v___f_3742_, v_xs_3740_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3744_, lean_object* v_x_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
if (lean_obj_tag(v_x_3744_) == 0)
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
v___x_3753_ = l_List_reverse___redArg(v_x_3745_);
v___x_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
return v___x_3754_;
}
else
{
lean_object* v_head_3755_; lean_object* v_tail_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3774_; 
v_head_3755_ = lean_ctor_get(v_x_3744_, 0);
v_tail_3756_ = lean_ctor_get(v_x_3744_, 1);
v_isSharedCheck_3774_ = !lean_is_exclusive(v_x_3744_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3758_ = v_x_3744_;
v_isShared_3759_ = v_isSharedCheck_3774_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_tail_3756_);
lean_inc(v_head_3755_);
lean_dec(v_x_3744_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3774_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3760_; 
lean_inc(v___y_3751_);
lean_inc_ref(v___y_3750_);
lean_inc(v___y_3749_);
lean_inc_ref(v___y_3748_);
lean_inc(v___y_3747_);
lean_inc_ref(v___y_3746_);
v___x_3760_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3755_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3761_);
lean_dec_ref(v___x_3760_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 1, v_x_3745_);
lean_ctor_set(v___x_3758_, 0, v_a_3761_);
v___x_3763_ = v___x_3758_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3761_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v_x_3745_);
v___x_3763_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
v_x_3744_ = v_tail_3756_;
v_x_3745_ = v___x_3763_;
goto _start;
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_del_object(v___x_3758_);
lean_dec(v_tail_3756_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v_x_3745_);
v_a_3766_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3760_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3760_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3775_, lean_object* v_x_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3775_, v_x_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3785_, uint8_t v_noDefaults_3786_, uint8_t v_star_3787_, lean_object* v_cfg_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
if (v_noDefaults_3786_ == 0)
{
goto v___jp_3796_;
}
else
{
if (v_star_3787_ == 0)
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v_remove_3785_);
v___x_3815_ = lean_box(0);
v___x_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
return v___x_3816_;
}
else
{
goto v___jp_3796_;
}
}
v___jp_3796_:
{
lean_object* v___x_3797_; 
lean_inc_ref(v___y_3791_);
v___x_3797_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref(v___x_3797_);
v___x_3799_ = lean_box(0);
lean_inc(v___y_3794_);
lean_inc_ref(v___y_3793_);
lean_inc(v___y_3792_);
lean_inc_ref(v___y_3791_);
v___x_3800_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3785_, v___x_3799_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_toApplyRulesConfig_3801_; lean_object* v_a_3802_; uint8_t v_symm_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v_toApplyRulesConfig_3801_ = lean_ctor_get(v_cfg_3788_, 0);
v_a_3802_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_a_3802_);
lean_dec_ref(v___x_3800_);
v_symm_3803_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3801_, sizeof(void*)*2 + 1);
v___x_3804_ = lean_array_to_list(v_a_3798_);
v___x_3805_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3804_, v_a_3802_);
v___x_3806_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3803_, v___x_3805_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
return v___x_3806_;
}
else
{
lean_dec(v_a_3798_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
return v___x_3800_;
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v_remove_3785_);
v_a_3807_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3797_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3797_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3817_, lean_object* v_noDefaults_3818_, lean_object* v_star_3819_, lean_object* v_cfg_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
uint8_t v_noDefaults_boxed_3828_; uint8_t v_star_boxed_3829_; lean_object* v_res_3830_; 
v_noDefaults_boxed_3828_ = lean_unbox(v_noDefaults_3818_);
v_star_boxed_3829_ = lean_unbox(v_star_3819_);
v_res_3830_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3817_, v_noDefaults_boxed_3828_, v_star_boxed_3829_, v_cfg_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec_ref(v_cfg_3820_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3831_, size_t v_i_3832_, size_t v_stop_3833_, lean_object* v_b_3834_){
_start:
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_usize_dec_eq(v_i_3832_, v_stop_3833_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; lean_object* v___x_3837_; size_t v___x_3838_; size_t v___x_3839_; 
v___x_3836_ = lean_array_uget_borrowed(v_as_3831_, v_i_3832_);
v___x_3837_ = l_Array_append___redArg(v_b_3834_, v___x_3836_);
v___x_3838_ = ((size_t)1ULL);
v___x_3839_ = lean_usize_add(v_i_3832_, v___x_3838_);
v_i_3832_ = v___x_3839_;
v_b_3834_ = v___x_3837_;
goto _start;
}
else
{
return v_b_3834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3841_, lean_object* v_i_3842_, lean_object* v_stop_3843_, lean_object* v_b_3844_){
_start:
{
size_t v_i_boxed_3845_; size_t v_stop_boxed_3846_; lean_object* v_res_3847_; 
v_i_boxed_3845_ = lean_unbox_usize(v_i_3842_);
lean_dec(v_i_3842_);
v_stop_boxed_3846_ = lean_unbox_usize(v_stop_3843_);
lean_dec(v_stop_3843_);
v_res_3847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3841_, v_i_boxed_3845_, v_stop_boxed_3846_, v_b_3844_);
lean_dec_ref(v_as_3841_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3848_, lean_object* v_a_3849_){
_start:
{
if (lean_obj_tag(v_a_3848_) == 0)
{
lean_object* v___x_3850_; 
v___x_3850_ = l_List_reverse___redArg(v_a_3849_);
return v___x_3850_;
}
else
{
lean_object* v_head_3851_; lean_object* v_tail_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3861_; 
v_head_3851_ = lean_ctor_get(v_a_3848_, 0);
v_tail_3852_ = lean_ctor_get(v_a_3848_, 1);
v_isSharedCheck_3861_ = !lean_is_exclusive(v_a_3848_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3854_ = v_a_3848_;
v_isShared_3855_ = v_isSharedCheck_3861_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_tail_3852_);
lean_inc(v_head_3851_);
lean_dec(v_a_3848_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3861_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3856_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3856_, 0, v_head_3851_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 1, v_a_3849_);
lean_ctor_set(v___x_3854_, 0, v___x_3856_);
v___x_3858_ = v___x_3854_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3860_, 1, v_a_3849_);
v___x_3858_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
v_a_3848_ = v_tail_3852_;
v_a_3849_ = v___x_3858_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3862_, size_t v_i_3863_, lean_object* v_bs_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
uint8_t v___x_3868_; 
v___x_3868_ = lean_usize_dec_lt(v_i_3863_, v_sz_3862_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3869_; 
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v_bs_3864_);
return v___x_3869_;
}
else
{
lean_object* v_v_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v_v_3870_ = lean_array_uget_borrowed(v_bs_3864_, v_i_3863_);
v___x_3871_ = l_Lean_Syntax_getId(v_v_3870_);
v___x_3872_ = l_Lean_labelled(v___x_3871_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___x_3874_; lean_object* v_bs_x27_3875_; size_t v___x_3876_; size_t v___x_3877_; lean_object* v___x_3878_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref(v___x_3872_);
v___x_3874_ = lean_unsigned_to_nat(0u);
v_bs_x27_3875_ = lean_array_uset(v_bs_3864_, v_i_3863_, v___x_3874_);
v___x_3876_ = ((size_t)1ULL);
v___x_3877_ = lean_usize_add(v_i_3863_, v___x_3876_);
v___x_3878_ = lean_array_uset(v_bs_x27_3875_, v_i_3863_, v_a_3873_);
v_i_3863_ = v___x_3877_;
v_bs_3864_ = v___x_3878_;
goto _start;
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec_ref(v_bs_3864_);
v_a_3880_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3872_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3872_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3888_, lean_object* v_i_3889_, lean_object* v_bs_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
size_t v_sz_boxed_3894_; size_t v_i_boxed_3895_; lean_object* v_res_3896_; 
v_sz_boxed_3894_ = lean_unbox_usize(v_sz_3888_);
lean_dec(v_sz_3888_);
v_i_boxed_3895_ = lean_unbox_usize(v_i_3889_);
lean_dec(v_i_3889_);
v_res_3896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3894_, v_i_boxed_3895_, v_bs_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3897_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
lean_dec(v___y_3912_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3915_, lean_object* v_a_3916_){
_start:
{
if (lean_obj_tag(v_a_3915_) == 0)
{
lean_object* v___x_3917_; 
v___x_3917_ = l_List_reverse___redArg(v_a_3916_);
return v___x_3917_;
}
else
{
lean_object* v_head_3918_; lean_object* v_tail_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3928_; 
v_head_3918_ = lean_ctor_get(v_a_3915_, 0);
v_tail_3919_ = lean_ctor_get(v_a_3915_, 1);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_a_3915_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3921_ = v_a_3915_;
v_isShared_3922_ = v_isSharedCheck_3928_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_tail_3919_);
lean_inc(v_head_3918_);
lean_dec(v_a_3915_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3928_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___f_3923_; lean_object* v___x_3925_; 
v___f_3923_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3923_, 0, v_head_3918_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 1, v_a_3916_);
lean_ctor_set(v___x_3921_, 0, v___f_3923_);
v___x_3925_ = v___x_3921_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___f_3923_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_a_3916_);
v___x_3925_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
v_a_3915_ = v_tail_3919_;
v_a_3916_ = v___x_3925_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3930_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3931_ = l_Lean_stringToMessageData(v___x_3930_);
return v___x_3931_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3934_ = l_String_toRawSubstring_x27(v___x_3933_);
return v___x_3934_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3939_ = l_String_toRawSubstring_x27(v___x_3938_);
return v___x_3939_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3943_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3944_ = l_String_toRawSubstring_x27(v___x_3943_);
return v___x_3944_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3948_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3949_ = l_String_toRawSubstring_x27(v___x_3948_);
return v___x_3949_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3979_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3980_ = l_Lean_stringToMessageData(v___x_3979_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3981_, uint8_t v_star_3982_, lean_object* v_add_3983_, lean_object* v_remove_3984_, lean_object* v_use_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___f_4016_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; 
v___x_4014_ = lean_box(v_noDefaults_3981_);
v___x_4015_ = lean_box(v_star_3982_);
lean_inc(v_remove_3984_);
v___f_4016_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_4016_, 0, v_remove_3984_);
lean_closure_set(v___f_4016_, 1, v___x_4014_);
lean_closure_set(v___f_4016_, 2, v___x_4015_);
if (v_star_3982_ == 0)
{
v___y_4033_ = v_a_3986_;
v___y_4034_ = v_a_3987_;
v___y_4035_ = v_a_3988_;
v___y_4036_ = v_a_3989_;
goto v___jp_4032_;
}
else
{
if (v_noDefaults_3981_ == 0)
{
lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec_ref(v___f_4016_);
lean_dec_ref(v_use_3985_);
lean_dec(v_remove_3984_);
lean_dec(v_add_3983_);
v___x_4095_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_4096_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_4095_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
lean_dec_ref(v_a_3988_);
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4096_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4096_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
else
{
v___y_4033_ = v_a_3986_;
v___y_4034_ = v_a_3987_;
v___y_4035_ = v_a_3988_;
v___y_4036_ = v_a_3989_;
goto v___jp_4032_;
}
}
v___jp_3991_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___y_3992_);
lean_ctor_set(v___x_3994_, 1, v___y_3993_);
v___x_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
return v___x_3995_;
}
v___jp_3996_:
{
uint8_t v___x_4003_; 
v___x_4003_ = l_List_isEmpty___redArg(v_remove_3984_);
lean_dec(v_remove_3984_);
if (v___x_4003_ == 0)
{
if (v_noDefaults_3981_ == 0)
{
lean_dec_ref(v___y_4000_);
v___y_3992_ = v___y_4002_;
v___y_3993_ = v___y_4001_;
goto v___jp_3991_;
}
else
{
if (v_star_3982_ == 0)
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
v___x_4004_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_4005_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_4004_, v___y_3999_, v___y_3997_, v___y_4000_, v___y_3998_);
lean_dec_ref(v___y_4000_);
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_4005_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
else
{
lean_dec_ref(v___y_4000_);
v___y_3992_ = v___y_4002_;
v___y_3993_ = v___y_4001_;
goto v___jp_3991_;
}
}
}
else
{
lean_dec_ref(v___y_4000_);
v___y_3992_ = v___y_4002_;
v___y_3993_ = v___y_4001_;
goto v___jp_3991_;
}
}
v___jp_4017_:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4025_ = lean_array_to_list(v___y_4024_);
lean_inc(v___y_4022_);
v___x_4026_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_4025_, v___y_4022_);
if (v_noDefaults_3981_ == 0)
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4027_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3983_, v___y_4022_);
v___x_4028_ = l_List_appendTR___redArg(v___x_4027_, v___x_4026_);
v___x_4029_ = l_List_appendTR___redArg(v___x_4028_, v___y_4021_);
v___y_3997_ = v___y_4018_;
v___y_3998_ = v___y_4019_;
v___y_3999_ = v___y_4020_;
v___y_4000_ = v___y_4023_;
v___y_4001_ = v___f_4016_;
v___y_4002_ = v___x_4029_;
goto v___jp_3996_;
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
lean_dec(v___y_4021_);
v___x_4030_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3983_, v___y_4022_);
v___x_4031_ = l_List_appendTR___redArg(v___x_4030_, v___x_4026_);
v___y_3997_ = v___y_4018_;
v___y_3998_ = v___y_4019_;
v___y_3999_ = v___y_4020_;
v___y_4000_ = v___y_4023_;
v___y_4001_ = v___f_4016_;
v___y_4002_ = v___x_4031_;
goto v___jp_3996_;
}
}
v___jp_4032_:
{
lean_object* v_ref_4037_; lean_object* v_quotContext_4038_; lean_object* v_currMacroScope_4039_; lean_object* v___x_4040_; lean_object* v_a_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v_a_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v_a_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; size_t v_sz_4053_; size_t v___x_4054_; lean_object* v___x_4055_; 
v_ref_4037_ = lean_ctor_get(v___y_4035_, 5);
v_quotContext_4038_ = lean_ctor_get(v___y_4035_, 10);
v_currMacroScope_4039_ = lean_ctor_get(v___y_4035_, 11);
v___x_4040_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref(v___x_4040_);
v___x_4042_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_4043_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref(v___x_4043_);
v___x_4045_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc(v_currMacroScope_4039_);
lean_inc(v_quotContext_4038_);
v___x_4046_ = l_Lean_addMacroScope(v_quotContext_4038_, v___x_4045_, v_currMacroScope_4039_);
v___x_4047_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_4048_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4049_);
lean_dec_ref(v___x_4048_);
v___x_4050_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
lean_inc(v_currMacroScope_4039_);
lean_inc(v_quotContext_4038_);
v___x_4051_ = l_Lean_addMacroScope(v_quotContext_4038_, v___x_4050_, v_currMacroScope_4039_);
v___x_4052_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_4053_ = lean_array_size(v_use_3985_);
v___x_4054_ = ((size_t)0ULL);
v___x_4055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4053_, v___x_4054_, v_use_3985_, v___y_4035_, v___y_4036_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; uint8_t v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; uint8_t v___x_4081_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref(v___x_4055_);
v___x_4057_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc(v_currMacroScope_4039_);
lean_inc(v_quotContext_4038_);
v___x_4058_ = l_Lean_addMacroScope(v_quotContext_4038_, v___x_4057_, v_currMacroScope_4039_);
v___x_4059_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_4060_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
lean_inc(v_currMacroScope_4039_);
lean_inc(v_quotContext_4038_);
v___x_4061_ = l_Lean_addMacroScope(v_quotContext_4038_, v___x_4060_, v_currMacroScope_4039_);
v___x_4062_ = 0;
v___x_4063_ = l_Lean_SourceInfo_fromRef(v_ref_4037_, v___x_4062_);
v___x_4064_ = lean_box(0);
v___x_4065_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_4066_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4063_);
lean_ctor_set(v___x_4066_, 1, v___x_4042_);
lean_ctor_set(v___x_4066_, 2, v___x_4046_);
lean_ctor_set(v___x_4066_, 3, v___x_4065_);
v___x_4067_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_4068_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4068_, 0, v_a_4041_);
lean_ctor_set(v___x_4068_, 1, v___x_4047_);
lean_ctor_set(v___x_4068_, 2, v___x_4051_);
lean_ctor_set(v___x_4068_, 3, v___x_4067_);
v___x_4069_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_4070_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4070_, 0, v_a_4044_);
lean_ctor_set(v___x_4070_, 1, v___x_4052_);
lean_ctor_set(v___x_4070_, 2, v___x_4058_);
lean_ctor_set(v___x_4070_, 3, v___x_4069_);
v___x_4071_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_4072_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4072_, 0, v_a_4049_);
lean_ctor_set(v___x_4072_, 1, v___x_4059_);
lean_ctor_set(v___x_4072_, 2, v___x_4061_);
lean_ctor_set(v___x_4072_, 3, v___x_4071_);
v___x_4073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
lean_ctor_set(v___x_4073_, 1, v___x_4064_);
v___x_4074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4070_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
v___x_4075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4068_);
lean_ctor_set(v___x_4075_, 1, v___x_4074_);
v___x_4076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4066_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
v___x_4077_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_4076_, v___x_4064_);
v___x_4078_ = lean_unsigned_to_nat(0u);
v___x_4079_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_4080_ = lean_array_get_size(v_a_4056_);
v___x_4081_ = lean_nat_dec_lt(v___x_4078_, v___x_4080_);
if (v___x_4081_ == 0)
{
lean_dec(v_a_4056_);
v___y_4018_ = v___y_4034_;
v___y_4019_ = v___y_4036_;
v___y_4020_ = v___y_4033_;
v___y_4021_ = v___x_4077_;
v___y_4022_ = v___x_4064_;
v___y_4023_ = v___y_4035_;
v___y_4024_ = v___x_4079_;
goto v___jp_4017_;
}
else
{
uint8_t v___x_4082_; 
v___x_4082_ = lean_nat_dec_le(v___x_4080_, v___x_4080_);
if (v___x_4082_ == 0)
{
if (v___x_4081_ == 0)
{
lean_dec(v_a_4056_);
v___y_4018_ = v___y_4034_;
v___y_4019_ = v___y_4036_;
v___y_4020_ = v___y_4033_;
v___y_4021_ = v___x_4077_;
v___y_4022_ = v___x_4064_;
v___y_4023_ = v___y_4035_;
v___y_4024_ = v___x_4079_;
goto v___jp_4017_;
}
else
{
size_t v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = lean_usize_of_nat(v___x_4080_);
v___x_4084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4056_, v___x_4054_, v___x_4083_, v___x_4079_);
lean_dec(v_a_4056_);
v___y_4018_ = v___y_4034_;
v___y_4019_ = v___y_4036_;
v___y_4020_ = v___y_4033_;
v___y_4021_ = v___x_4077_;
v___y_4022_ = v___x_4064_;
v___y_4023_ = v___y_4035_;
v___y_4024_ = v___x_4084_;
goto v___jp_4017_;
}
}
else
{
size_t v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = lean_usize_of_nat(v___x_4080_);
v___x_4086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4056_, v___x_4054_, v___x_4085_, v___x_4079_);
lean_dec(v_a_4056_);
v___y_4018_ = v___y_4034_;
v___y_4019_ = v___y_4036_;
v___y_4020_ = v___y_4033_;
v___y_4021_ = v___x_4077_;
v___y_4022_ = v___x_4064_;
v___y_4023_ = v___y_4035_;
v___y_4024_ = v___x_4086_;
goto v___jp_4017_;
}
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_dec(v___x_4051_);
lean_dec(v_a_4049_);
lean_dec(v___x_4046_);
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v___y_4035_);
lean_dec_ref(v___f_4016_);
lean_dec(v_remove_3984_);
lean_dec(v_add_3983_);
v_a_4087_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4055_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4055_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_4105_, lean_object* v_star_4106_, lean_object* v_add_4107_, lean_object* v_remove_4108_, lean_object* v_use_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_){
_start:
{
uint8_t v_noDefaults_boxed_4115_; uint8_t v_star_boxed_4116_; lean_object* v_res_4117_; 
v_noDefaults_boxed_4115_ = lean_unbox(v_noDefaults_4105_);
v_star_boxed_4116_ = lean_unbox(v_star_4106_);
v_res_4117_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_4115_, v_star_boxed_4116_, v_add_4107_, v_remove_4108_, v_use_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
lean_dec(v_a_4113_);
lean_dec(v_a_4111_);
lean_dec_ref(v_a_4110_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t v_sz_4118_, size_t v_i_4119_, lean_object* v_bs_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v___x_4126_; 
v___x_4126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4118_, v_i_4119_, v_bs_4120_, v___y_4123_, v___y_4124_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_sz_4127_, lean_object* v_i_4128_, lean_object* v_bs_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
size_t v_sz_boxed_4135_; size_t v_i_boxed_4136_; lean_object* v_res_4137_; 
v_sz_boxed_4135_ = lean_unbox_usize(v_sz_4127_);
lean_dec(v_sz_4127_);
v_i_boxed_4136_ = lean_unbox_usize(v_i_4128_);
lean_dec(v_i_4128_);
v_res_4137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_4135_, v_i_boxed_4136_, v_bs_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
return v_res_4137_;
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
