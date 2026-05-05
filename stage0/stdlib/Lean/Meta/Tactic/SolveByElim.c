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
v___x_776_ = lean_float_of_nat(v___y_773_);
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
v___x_785_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_699_, v___x_700_, v___x_701_, v_options_708_, v___x_770_, v___y_772_, v___f_702_, v___x_784_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
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
v___x_809_ = lean_float_of_nat(v___y_806_);
v___x_810_ = lean_float_of_nat(v___x_808_);
v___x_811_ = lean_box_float(v___x_809_);
v___x_812_ = lean_box_float(v___x_810_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_a_807_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_699_, v___x_700_, v___x_701_, v_options_708_, v___x_770_, v___y_805_, v___f_702_, v___x_814_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_815_;
}
v___jp_816_:
{
lean_object* v___x_820_; 
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v_a_819_);
v___y_805_ = v___y_818_;
v___y_806_ = v___y_817_;
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
v___y_817_ = v___y_823_;
v___y_818_ = v___y_822_;
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
v___y_787_ = v_a_836_;
v___y_788_ = v___x_839_;
v_a_789_ = v___x_887_;
goto v___jp_786_;
}
else
{
v___y_792_ = v_a_836_;
v___y_793_ = v___x_839_;
v___y_794_ = v___x_885_;
goto v___jp_791_;
}
}
else
{
v___y_792_ = v_a_836_;
v___y_793_ = v___x_839_;
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
v___y_822_ = v_a_836_;
v___y_823_ = v___x_890_;
v___y_824_ = v___x_936_;
goto v___jp_821_;
}
}
else
{
v___y_822_ = v_a_836_;
v___y_823_ = v___x_890_;
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
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2150_){
_start:
{
if (lean_obj_tag(v_x_2150_) == 0)
{
uint8_t v___x_2151_; 
v___x_2151_ = 0;
return v___x_2151_;
}
else
{
lean_object* v_head_2152_; lean_object* v_tail_2153_; uint8_t v___x_2154_; 
v_head_2152_ = lean_ctor_get(v_x_2150_, 0);
v_tail_2153_ = lean_ctor_get(v_x_2150_, 1);
v___x_2154_ = l_Lean_Expr_hasMVar(v_head_2152_);
if (v___x_2154_ == 0)
{
v_x_2150_ = v_tail_2153_;
goto _start;
}
else
{
return v___x_2154_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2156_){
_start:
{
uint8_t v_res_2157_; lean_object* v_r_2158_; 
v_res_2157_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2156_);
lean_dec(v_x_2156_);
v_r_2158_ = lean_box(v_res_2157_);
return v_r_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2159_, lean_object* v_sols_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v___x_2166_; 
v___x_2166_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2160_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; 
lean_inc(v___y_2164_);
lean_inc_ref(v___y_2163_);
lean_inc(v___y_2162_);
lean_inc_ref(v___y_2161_);
v___x_2167_ = lean_apply_6(v_test_2159_, v_sols_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, lean_box(0));
return v___x_2167_;
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec(v_sols_2160_);
lean_dec_ref(v_test_2159_);
v___x_2168_ = lean_box(v___x_2166_);
v___x_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
return v___x_2169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2170_, lean_object* v_sols_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2170_, v_sols_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2178_, lean_object* v_test_2179_){
_start:
{
lean_object* v___f_2180_; lean_object* v___x_2181_; 
v___f_2180_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2180_, 0, v_test_2179_);
v___x_2181_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2178_, v___f_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2182_, lean_object* v_x_2183_){
_start:
{
if (lean_obj_tag(v_x_2183_) == 0)
{
uint8_t v___x_2184_; 
lean_dec_ref(v_e_2182_);
v___x_2184_ = 0;
return v___x_2184_;
}
else
{
lean_object* v_head_2185_; lean_object* v_tail_2186_; uint8_t v___x_2187_; 
v_head_2185_ = lean_ctor_get(v_x_2183_, 0);
v_tail_2186_ = lean_ctor_get(v_x_2183_, 1);
lean_inc_ref(v_e_2182_);
v___x_2187_ = l_Lean_Expr_occurs(v_e_2182_, v_head_2185_);
if (v___x_2187_ == 0)
{
v_x_2183_ = v_tail_2186_;
goto _start;
}
else
{
lean_dec_ref(v_e_2182_);
return v___x_2187_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2189_, lean_object* v_x_2190_){
_start:
{
uint8_t v_res_2191_; lean_object* v_r_2192_; 
v_res_2191_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2189_, v_x_2190_);
lean_dec(v_x_2190_);
v_r_2192_ = lean_box(v_res_2191_);
return v_r_2192_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2193_, lean_object* v_x_2194_){
_start:
{
if (lean_obj_tag(v_x_2194_) == 0)
{
uint8_t v___x_2195_; 
v___x_2195_ = 1;
return v___x_2195_;
}
else
{
lean_object* v_head_2196_; lean_object* v_tail_2197_; uint8_t v___x_2198_; 
v_head_2196_ = lean_ctor_get(v_x_2194_, 0);
lean_inc(v_head_2196_);
v_tail_2197_ = lean_ctor_get(v_x_2194_, 1);
lean_inc(v_tail_2197_);
lean_dec_ref(v_x_2194_);
v___x_2198_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2196_, v_sols_2193_);
if (v___x_2198_ == 0)
{
lean_dec(v_tail_2197_);
return v___x_2198_;
}
else
{
v_x_2194_ = v_tail_2197_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2200_, lean_object* v_x_2201_){
_start:
{
uint8_t v_res_2202_; lean_object* v_r_2203_; 
v_res_2202_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2200_, v_x_2201_);
lean_dec(v_sols_2200_);
v_r_2203_ = lean_box(v_res_2202_);
return v_r_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2204_, lean_object* v_sols_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
uint8_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2205_, v_use_2204_);
v___x_2212_ = lean_box(v___x_2211_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2214_, lean_object* v_sols_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2214_, v_sols_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v_sols_2215_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2222_, lean_object* v_use_2223_){
_start:
{
lean_object* v___f_2224_; lean_object* v___x_2225_; 
v___f_2224_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2224_, 0, v_use_2223_);
v___x_2225_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2222_, v___f_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2226_){
_start:
{
lean_object* v___y_2228_; lean_object* v_toApplyRulesConfig_2229_; uint8_t v_backtracking_2230_; uint8_t v_intro_2231_; uint8_t v_constructor_2232_; uint8_t v_suggestions_2233_; uint8_t v_intro_2237_; 
v_intro_2237_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*1 + 1);
if (v_intro_2237_ == 0)
{
lean_object* v_toApplyRulesConfig_2238_; uint8_t v_backtracking_2239_; uint8_t v_constructor_2240_; uint8_t v_suggestions_2241_; 
v_toApplyRulesConfig_2238_ = lean_ctor_get(v_cfg_2226_, 0);
lean_inc_ref(v_toApplyRulesConfig_2238_);
v_backtracking_2239_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*1);
v_constructor_2240_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*1 + 2);
v_suggestions_2241_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*1 + 3);
v___y_2228_ = v_cfg_2226_;
v_toApplyRulesConfig_2229_ = v_toApplyRulesConfig_2238_;
v_backtracking_2230_ = v_backtracking_2239_;
v_intro_2231_ = v_intro_2237_;
v_constructor_2232_ = v_constructor_2240_;
v_suggestions_2233_ = v_suggestions_2241_;
goto v___jp_2227_;
}
else
{
lean_object* v_toApplyRulesConfig_2242_; uint8_t v_backtracking_2243_; uint8_t v_constructor_2244_; uint8_t v_suggestions_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2259_; 
v_toApplyRulesConfig_2242_ = lean_ctor_get(v_cfg_2226_, 0);
v_backtracking_2243_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*1);
v_constructor_2244_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*1 + 2);
v_suggestions_2245_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*1 + 3);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_cfg_2226_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2247_ = v_cfg_2226_;
v_isShared_2248_ = v_isSharedCheck_2259_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_toApplyRulesConfig_2242_);
lean_dec(v_cfg_2226_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2259_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
uint8_t v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = 0;
if (v_isShared_2248_ == 0)
{
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_toApplyRulesConfig_2242_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*1, v_backtracking_2243_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*1 + 2, v_constructor_2244_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*1 + 3, v_suggestions_2245_);
v___x_2251_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2252_; lean_object* v_toApplyRulesConfig_2253_; uint8_t v_backtracking_2254_; uint8_t v_intro_2255_; uint8_t v_constructor_2256_; uint8_t v_suggestions_2257_; 
lean_ctor_set_uint8(v___x_2251_, sizeof(void*)*1 + 1, v___x_2249_);
v___x_2252_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2251_);
v_toApplyRulesConfig_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc_ref(v_toApplyRulesConfig_2253_);
v_backtracking_2254_ = lean_ctor_get_uint8(v___x_2252_, sizeof(void*)*1);
v_intro_2255_ = lean_ctor_get_uint8(v___x_2252_, sizeof(void*)*1 + 1);
v_constructor_2256_ = lean_ctor_get_uint8(v___x_2252_, sizeof(void*)*1 + 2);
v_suggestions_2257_ = lean_ctor_get_uint8(v___x_2252_, sizeof(void*)*1 + 3);
v___y_2228_ = v___x_2252_;
v_toApplyRulesConfig_2229_ = v_toApplyRulesConfig_2253_;
v_backtracking_2230_ = v_backtracking_2254_;
v_intro_2231_ = v_intro_2255_;
v_constructor_2232_ = v_constructor_2256_;
v_suggestions_2233_ = v_suggestions_2257_;
goto v___jp_2227_;
}
}
}
v___jp_2227_:
{
if (v_constructor_2232_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2229_);
return v___y_2228_;
}
else
{
uint8_t v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_dec_ref(v___y_2228_);
v___x_2234_ = 0;
v___x_2235_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2235_, 0, v_toApplyRulesConfig_2229_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*1, v_backtracking_2230_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*1 + 1, v_intro_2231_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*1 + 2, v___x_2234_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*1 + 3, v_suggestions_2233_);
v___x_2236_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2235_);
return v___x_2236_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2260_, lean_object* v_x_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
if (lean_obj_tag(v_x_2260_) == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = l_List_reverse___redArg(v_x_2261_);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
else
{
lean_object* v_head_2271_; lean_object* v_tail_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2290_; 
v_head_2271_ = lean_ctor_get(v_x_2260_, 0);
v_tail_2272_ = lean_ctor_get(v_x_2260_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_x_2260_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2274_ = v_x_2260_;
v_isShared_2275_ = v_isSharedCheck_2290_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_tail_2272_);
lean_inc(v_head_2271_);
lean_dec(v_x_2260_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2290_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; 
lean_inc(v___y_2267_);
lean_inc_ref(v___y_2266_);
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
lean_inc(v___y_2263_);
lean_inc_ref(v___y_2262_);
v___x_2276_ = lean_apply_7(v_head_2271_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, lean_box(0));
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref(v___x_2276_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 1, v_x_2261_);
lean_ctor_set(v___x_2274_, 0, v_a_2277_);
v___x_2279_ = v___x_2274_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2277_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_x_2261_);
v___x_2279_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
v_x_2260_ = v_tail_2272_;
v_x_2261_ = v___x_2279_;
goto _start;
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_del_object(v___x_2274_);
lean_dec(v_tail_2272_);
lean_dec(v_x_2261_);
v_a_2282_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2276_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2276_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2291_, lean_object* v_x_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2291_, v_x_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2301_, lean_object* v_cfg_2302_, lean_object* v_lemmas_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; 
lean_inc(v___y_2309_);
lean_inc_ref(v___y_2308_);
lean_inc(v___y_2307_);
lean_inc_ref(v___y_2306_);
lean_inc(v___y_2305_);
lean_inc_ref(v___y_2304_);
v___x_2311_ = lean_apply_8(v_ctx_2301_, v_cfg_2302_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, lean_box(0));
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref(v___x_2311_);
v___x_2313_ = lean_box(0);
v___x_2314_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2303_, v___x_2313_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2323_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2317_ = v___x_2314_;
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2314_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2319_ = l_List_appendTR___redArg(v_a_2312_, v_a_2315_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v___x_2319_);
v___x_2321_ = v___x_2317_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
else
{
lean_dec(v_a_2312_);
return v___x_2314_;
}
}
else
{
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v_lemmas_2303_);
return v___x_2311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2324_, lean_object* v_cfg_2325_, lean_object* v_lemmas_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2324_, v_cfg_2325_, v_lemmas_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
return v_res_2334_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2335_){
_start:
{
uint8_t v___x_2336_; 
v___x_2336_ = 0;
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2337_){
_start:
{
uint8_t v_res_2338_; lean_object* v_r_2339_; 
v_res_2338_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2337_);
lean_dec(v_x_2337_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2340_, lean_object* v___x_2341_, lean_object* v___x_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2340_, v___x_2341_, v___x_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2357_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2357_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2357_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v_fst_2353_; lean_object* v___x_2355_; 
v_fst_2353_ = lean_ctor_get(v_a_2349_, 0);
lean_inc(v_fst_2353_);
lean_dec(v_a_2349_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v_fst_2353_);
v___x_2355_ = v___x_2351_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_fst_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2348_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2348_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2366_, lean_object* v___x_2367_, lean_object* v___x_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2366_, v___x_2367_, v___x_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2389_, lean_object* v_g_2390_, lean_object* v_lemmas_2391_, lean_object* v_ctx_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v___f_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___f_2401_; lean_object* v___x_2402_; 
v___f_2398_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2398_, 0, v_ctx_2392_);
lean_closure_set(v___f_2398_, 1, v_cfg_2389_);
lean_closure_set(v___f_2398_, 2, v_lemmas_2391_);
v___x_2399_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2400_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2401_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2401_, 0, v___f_2398_);
lean_closure_set(v___f_2401_, 1, v___x_2399_);
lean_closure_set(v___f_2401_, 2, v___x_2400_);
v___x_2402_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2390_, v___f_2401_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2403_, lean_object* v_g_2404_, lean_object* v_lemmas_2405_, lean_object* v_ctx_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2403_, v_g_2404_, v_lemmas_2405_, v_ctx_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2413_, lean_object* v_lemmas_2414_, lean_object* v_ctx_2415_, lean_object* v_g_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
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
v___x_2427_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2425_, v_transparency_2426_, v_a_2424_, v_g_2416_, v_a_2418_, v_a_2420_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2436_, lean_object* v_lemmas_2437_, lean_object* v_ctx_2438_, lean_object* v_g_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2436_, v_lemmas_2437_, v_ctx_2438_, v_g_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2446_, lean_object* v_lemmas_2447_, lean_object* v_ctx_2448_, lean_object* v_g_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v___x_2455_; 
lean_inc(v_g_2449_);
lean_inc_ref(v_cfg_2446_);
v___x_2455_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2446_, v_g_2449_, v_lemmas_2447_, v_ctx_2448_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_toApplyRulesConfig_2456_; lean_object* v_a_2457_; lean_object* v_toApplyConfig_2458_; uint8_t v_transparency_2459_; lean_object* v___x_2460_; 
v_toApplyRulesConfig_2456_ = lean_ctor_get(v_cfg_2446_, 0);
lean_inc_ref(v_toApplyRulesConfig_2456_);
lean_dec_ref(v_cfg_2446_);
v_a_2457_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2457_);
lean_dec_ref(v___x_2455_);
v_toApplyConfig_2458_ = lean_ctor_get(v_toApplyRulesConfig_2456_, 1);
lean_inc_ref(v_toApplyConfig_2458_);
v_transparency_2459_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2456_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2456_);
v___x_2460_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2458_, v_transparency_2459_, v_a_2457_, v_g_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
return v___x_2460_;
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_g_2449_);
lean_dec_ref(v_cfg_2446_);
v_a_2461_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2455_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2455_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2469_, lean_object* v_lemmas_2470_, lean_object* v_ctx_2471_, lean_object* v_g_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2469_, v_lemmas_2470_, v_ctx_2471_, v_g_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
return v_res_2478_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2479_, lean_object* v_i_2480_, lean_object* v_k_2481_){
_start:
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = lean_array_get_size(v_keys_2479_);
v___x_2483_ = lean_nat_dec_lt(v_i_2480_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_dec(v_i_2480_);
return v___x_2483_;
}
else
{
lean_object* v_k_x27_2484_; uint8_t v___x_2485_; 
v_k_x27_2484_ = lean_array_fget_borrowed(v_keys_2479_, v_i_2480_);
v___x_2485_ = l_Lean_instBEqMVarId_beq(v_k_2481_, v_k_x27_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_unsigned_to_nat(1u);
v___x_2487_ = lean_nat_add(v_i_2480_, v___x_2486_);
lean_dec(v_i_2480_);
v_i_2480_ = v___x_2487_;
goto _start;
}
else
{
lean_dec(v_i_2480_);
return v___x_2485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2489_, lean_object* v_i_2490_, lean_object* v_k_2491_){
_start:
{
uint8_t v_res_2492_; lean_object* v_r_2493_; 
v_res_2492_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2489_, v_i_2490_, v_k_2491_);
lean_dec(v_k_2491_);
lean_dec_ref(v_keys_2489_);
v_r_2493_ = lean_box(v_res_2492_);
return v_r_2493_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2494_, size_t v_x_2495_, lean_object* v_x_2496_){
_start:
{
if (lean_obj_tag(v_x_2494_) == 0)
{
lean_object* v_es_2497_; lean_object* v___x_2498_; size_t v___x_2499_; size_t v___x_2500_; size_t v___x_2501_; lean_object* v_j_2502_; lean_object* v___x_2503_; 
v_es_2497_ = lean_ctor_get(v_x_2494_, 0);
v___x_2498_ = lean_box(2);
v___x_2499_ = ((size_t)5ULL);
v___x_2500_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2501_ = lean_usize_land(v_x_2495_, v___x_2500_);
v_j_2502_ = lean_usize_to_nat(v___x_2501_);
v___x_2503_ = lean_array_get_borrowed(v___x_2498_, v_es_2497_, v_j_2502_);
lean_dec(v_j_2502_);
switch(lean_obj_tag(v___x_2503_))
{
case 0:
{
lean_object* v_key_2504_; uint8_t v___x_2505_; 
v_key_2504_ = lean_ctor_get(v___x_2503_, 0);
v___x_2505_ = l_Lean_instBEqMVarId_beq(v_x_2496_, v_key_2504_);
return v___x_2505_;
}
case 1:
{
lean_object* v_node_2506_; size_t v___x_2507_; 
v_node_2506_ = lean_ctor_get(v___x_2503_, 0);
v___x_2507_ = lean_usize_shift_right(v_x_2495_, v___x_2499_);
v_x_2494_ = v_node_2506_;
v_x_2495_ = v___x_2507_;
goto _start;
}
default: 
{
uint8_t v___x_2509_; 
v___x_2509_ = 0;
return v___x_2509_;
}
}
}
else
{
lean_object* v_ks_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v_ks_2510_ = lean_ctor_get(v_x_2494_, 0);
v___x_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2510_, v___x_2511_, v_x_2496_);
return v___x_2512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2513_, lean_object* v_x_2514_, lean_object* v_x_2515_){
_start:
{
size_t v_x_2218__boxed_2516_; uint8_t v_res_2517_; lean_object* v_r_2518_; 
v_x_2218__boxed_2516_ = lean_unbox_usize(v_x_2514_);
lean_dec(v_x_2514_);
v_res_2517_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2513_, v_x_2218__boxed_2516_, v_x_2515_);
lean_dec(v_x_2515_);
lean_dec_ref(v_x_2513_);
v_r_2518_ = lean_box(v_res_2517_);
return v_r_2518_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2519_, lean_object* v_x_2520_){
_start:
{
uint64_t v___x_2521_; size_t v___x_2522_; uint8_t v___x_2523_; 
v___x_2521_ = l_Lean_instHashableMVarId_hash(v_x_2520_);
v___x_2522_ = lean_uint64_to_usize(v___x_2521_);
v___x_2523_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2519_, v___x_2522_, v_x_2520_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2524_, lean_object* v_x_2525_){
_start:
{
uint8_t v_res_2526_; lean_object* v_r_2527_; 
v_res_2526_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2524_, v_x_2525_);
lean_dec(v_x_2525_);
lean_dec_ref(v_x_2524_);
v_r_2527_ = lean_box(v_res_2526_);
return v_r_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v___x_2531_; lean_object* v_mctx_2532_; lean_object* v_eAssignment_2533_; uint8_t v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2531_ = lean_st_ref_get(v___y_2529_);
v_mctx_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc_ref(v_mctx_2532_);
lean_dec(v___x_2531_);
v_eAssignment_2533_ = lean_ctor_get(v_mctx_2532_, 8);
lean_inc_ref(v_eAssignment_2533_);
lean_dec_ref(v_mctx_2532_);
v___x_2534_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2533_, v_mvarId_2528_);
lean_dec_ref(v_eAssignment_2533_);
v___x_2535_ = lean_box(v___x_2534_);
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec(v_mvarId_2537_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2541_, lean_object* v_x_2542_){
_start:
{
if (lean_obj_tag(v_x_2542_) == 0)
{
return v_x_2541_;
}
else
{
lean_object* v_head_2543_; lean_object* v_tail_2544_; lean_object* v___x_2545_; 
v_head_2543_ = lean_ctor_get(v_x_2542_, 0);
lean_inc(v_head_2543_);
v_tail_2544_ = lean_ctor_get(v_x_2542_, 1);
lean_inc(v_tail_2544_);
lean_dec_ref(v_x_2542_);
v___x_2545_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2541_, v_head_2543_);
v_x_2541_ = v___x_2545_;
v_x_2542_ = v_tail_2544_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2547_, lean_object* v_a_2548_, uint8_t v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
if (lean_obj_tag(v_a_2550_) == 0)
{
if (lean_obj_tag(v_a_2551_) == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_dec(v_a_2548_);
lean_dec_ref(v_f_2547_);
v___x_2558_ = lean_box(v_a_2549_);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v_a_2552_);
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
else
{
lean_object* v_head_2561_; lean_object* v_tail_2562_; 
v_head_2561_ = lean_ctor_get(v_a_2551_, 0);
lean_inc(v_head_2561_);
v_tail_2562_ = lean_ctor_get(v_a_2551_, 1);
lean_inc(v_tail_2562_);
lean_dec_ref(v_a_2551_);
v_a_2550_ = v_head_2561_;
v_a_2551_ = v_tail_2562_;
goto _start;
}
}
else
{
lean_object* v_head_2564_; lean_object* v_tail_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2608_; 
v_head_2564_ = lean_ctor_get(v_a_2550_, 0);
v_tail_2565_ = lean_ctor_get(v_a_2550_, 1);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_a_2550_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2567_ = v_a_2550_;
v_isShared_2568_ = v_isSharedCheck_2608_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_tail_2565_);
lean_inc(v_head_2564_);
lean_dec(v_a_2550_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2608_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2607_; 
v___x_2569_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2564_, v___y_2554_);
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2607_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2607_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
uint8_t v___x_2574_; 
v___x_2574_ = lean_unbox(v_a_2570_);
lean_dec(v_a_2570_);
if (v___x_2574_ == 0)
{
lean_object* v_zero_2575_; uint8_t v_isZero_2576_; 
v_zero_2575_ = lean_unsigned_to_nat(0u);
v_isZero_2576_ = lean_nat_dec_eq(v_a_2548_, v_zero_2575_);
if (v_isZero_2576_ == 1)
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; 
lean_del_object(v___x_2567_);
lean_dec(v_a_2548_);
lean_dec_ref(v_f_2547_);
v___x_2577_ = lean_array_push(v_a_2552_, v_head_2564_);
v___x_2578_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2577_, v_tail_2565_);
v___x_2579_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2578_, v_a_2551_);
v___x_2580_ = lean_box(v_a_2549_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v___x_2579_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2581_);
v___x_2583_ = v___x_2572_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_del_object(v___x_2572_);
lean_inc_ref(v_f_2547_);
lean_inc(v_head_2564_);
v___x_2585_ = lean_apply_1(v_f_2547_, v_head_2564_);
v___x_2586_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2585_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v_one_2588_; lean_object* v_n_2589_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref(v___x_2586_);
v_one_2588_ = lean_unsigned_to_nat(1u);
v_n_2589_ = lean_nat_sub(v_a_2548_, v_one_2588_);
lean_dec(v_a_2548_);
if (lean_obj_tag(v_a_2587_) == 0)
{
lean_object* v___x_2590_; 
lean_del_object(v___x_2567_);
v___x_2590_ = lean_array_push(v_a_2552_, v_head_2564_);
v_a_2548_ = v_n_2589_;
v_a_2550_ = v_tail_2565_;
v_a_2552_ = v___x_2590_;
goto _start;
}
else
{
lean_object* v_val_2592_; uint8_t v___x_2593_; lean_object* v___x_2595_; 
lean_dec(v_head_2564_);
v_val_2592_ = lean_ctor_get(v_a_2587_, 0);
lean_inc(v_val_2592_);
lean_dec_ref(v_a_2587_);
v___x_2593_ = 1;
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 1, v_a_2551_);
lean_ctor_set(v___x_2567_, 0, v_tail_2565_);
v___x_2595_ = v___x_2567_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_tail_2565_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_a_2551_);
v___x_2595_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
v_a_2548_ = v_n_2589_;
v_a_2549_ = v___x_2593_;
v_a_2550_ = v_val_2592_;
v_a_2551_ = v___x_2595_;
goto _start;
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_del_object(v___x_2567_);
lean_dec(v_tail_2565_);
lean_dec(v_head_2564_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec(v_a_2548_);
lean_dec_ref(v_f_2547_);
v_a_2598_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2586_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2586_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
else
{
lean_del_object(v___x_2572_);
lean_del_object(v___x_2567_);
lean_dec(v_head_2564_);
v_a_2550_ = v_tail_2565_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
uint8_t v_a_2299__boxed_2620_; lean_object* v_res_2621_; 
v_a_2299__boxed_2620_ = lean_unbox(v_a_2611_);
v_res_2621_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2609_, v_a_2610_, v_a_2299__boxed_2620_, v_a_2612_, v_a_2613_, v_a_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2622_, size_t v_i_2623_, size_t v_stop_2624_, lean_object* v_b_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_a_2632_; uint8_t v___x_2636_; 
v___x_2636_ = lean_usize_dec_eq(v_i_2623_, v_stop_2624_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; lean_object* v___x_2640_; 
v___x_2637_ = lean_array_uget_borrowed(v_as_2622_, v_i_2623_);
v___x_2640_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2637_, v___y_2627_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; uint8_t v___x_2642_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref(v___x_2640_);
v___x_2642_ = lean_unbox(v_a_2641_);
lean_dec(v_a_2641_);
if (v___x_2642_ == 0)
{
goto v___jp_2638_;
}
else
{
v_a_2632_ = v_b_2625_;
goto v___jp_2631_;
}
}
else
{
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2643_; uint8_t v___x_2644_; 
v_a_2643_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2643_);
lean_dec_ref(v___x_2640_);
v___x_2644_ = lean_unbox(v_a_2643_);
lean_dec(v_a_2643_);
if (v___x_2644_ == 0)
{
v_a_2632_ = v_b_2625_;
goto v___jp_2631_;
}
else
{
goto v___jp_2638_;
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec_ref(v_b_2625_);
v_a_2645_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2640_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2640_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
v___jp_2638_:
{
lean_object* v___x_2639_; 
lean_inc(v___x_2637_);
v___x_2639_ = lean_array_push(v_b_2625_, v___x_2637_);
v_a_2632_ = v___x_2639_;
goto v___jp_2631_;
}
}
else
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v_b_2625_);
return v___x_2653_;
}
v___jp_2631_:
{
size_t v___x_2633_; size_t v___x_2634_; 
v___x_2633_ = ((size_t)1ULL);
v___x_2634_ = lean_usize_add(v_i_2623_, v___x_2633_);
v_i_2623_ = v___x_2634_;
v_b_2625_ = v_a_2632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2654_, lean_object* v_i_2655_, lean_object* v_stop_2656_, lean_object* v_b_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
size_t v_i_boxed_2663_; size_t v_stop_boxed_2664_; lean_object* v_res_2665_; 
v_i_boxed_2663_ = lean_unbox_usize(v_i_2655_);
lean_dec(v_i_2655_);
v_stop_boxed_2664_ = lean_unbox_usize(v_stop_2656_);
lean_dec(v_stop_2656_);
v_res_2665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2654_, v_i_boxed_2663_, v_stop_boxed_2664_, v_b_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec_ref(v_as_2654_);
return v_res_2665_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2669_ = lean_array_to_list(v___x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2670_, lean_object* v_goals_2671_, lean_object* v_maxIters_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
uint8_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2678_ = 0;
v___x_2679_ = lean_box(0);
v___x_2680_ = lean_unsigned_to_nat(0u);
v___x_2681_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2682_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2670_, v_maxIters_2672_, v___x_2678_, v_goals_2671_, v___x_2679_, v___x_2681_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2732_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2732_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2732_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v_fst_2687_; lean_object* v_snd_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2731_; 
v_fst_2687_ = lean_ctor_get(v_a_2683_, 0);
v_snd_2688_ = lean_ctor_get(v_a_2683_, 1);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_a_2683_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2690_ = v_a_2683_;
v_isShared_2691_ = v_isSharedCheck_2731_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_snd_2688_);
lean_inc(v_fst_2687_);
lean_dec(v_a_2683_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2731_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_____do__lift_2693_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2701_ = lean_array_get_size(v_snd_2688_);
v___x_2702_ = lean_nat_dec_lt(v___x_2680_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
lean_del_object(v___x_2690_);
lean_dec(v_snd_2688_);
lean_del_object(v___x_2685_);
v___x_2703_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_fst_2687_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
return v___x_2705_;
}
else
{
uint8_t v___x_2706_; 
v___x_2706_ = lean_nat_dec_le(v___x_2701_, v___x_2701_);
if (v___x_2706_ == 0)
{
if (v___x_2702_ == 0)
{
lean_dec(v_snd_2688_);
v_____do__lift_2693_ = v___x_2681_;
goto v___jp_2692_;
}
else
{
size_t v___x_2707_; size_t v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = ((size_t)0ULL);
v___x_2708_ = lean_usize_of_nat(v___x_2701_);
v___x_2709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2688_, v___x_2707_, v___x_2708_, v___x_2681_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v_snd_2688_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref(v___x_2709_);
v_____do__lift_2693_ = v_a_2710_;
goto v___jp_2692_;
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_del_object(v___x_2690_);
lean_dec(v_fst_2687_);
lean_del_object(v___x_2685_);
v_a_2711_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2709_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2709_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
else
{
size_t v___x_2719_; size_t v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = ((size_t)0ULL);
v___x_2720_ = lean_usize_of_nat(v___x_2701_);
v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2688_, v___x_2719_, v___x_2720_, v___x_2681_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v_snd_2688_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2722_);
lean_dec_ref(v___x_2721_);
v_____do__lift_2693_ = v_a_2722_;
goto v___jp_2692_;
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_del_object(v___x_2690_);
lean_dec(v_fst_2687_);
lean_del_object(v___x_2685_);
v_a_2723_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2721_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2721_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
v___jp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2694_ = lean_array_to_list(v_____do__lift_2693_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 1, v___x_2694_);
v___x_2696_ = v___x_2690_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_fst_2687_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v___x_2696_);
v___x_2698_ = v___x_2685_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
v_a_2733_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2682_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2682_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2741_, lean_object* v_goals_2742_, lean_object* v_maxIters_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2741_, v_goals_2742_, v_maxIters_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
return v_res_2749_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2752_ = l_Lean_stringToMessageData(v___x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2753_, lean_object* v_goals_2754_, lean_object* v_maxIters_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2753_, v_goals_2754_, v_maxIters_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2774_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2774_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2774_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_fst_2766_; uint8_t v___x_2767_; 
v_fst_2766_ = lean_ctor_get(v_a_2762_, 0);
v___x_2767_ = lean_unbox(v_fst_2766_);
if (v___x_2767_ == 1)
{
lean_object* v_snd_2768_; lean_object* v___x_2770_; 
v_snd_2768_ = lean_ctor_get(v_a_2762_, 1);
lean_inc(v_snd_2768_);
lean_dec(v_a_2762_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v_snd_2768_);
v___x_2770_ = v___x_2764_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_snd_2768_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
else
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_del_object(v___x_2764_);
lean_dec(v_a_2762_);
v___x_2772_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2773_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2772_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
return v___x_2773_;
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
v_a_2775_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2761_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2761_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2783_, lean_object* v_goals_2784_, lean_object* v_maxIters_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2783_, v_goals_2784_, v_maxIters_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2792_, lean_object* v_ctx_2793_, lean_object* v_cfg_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
uint8_t v_backtracking_2801_; 
v_backtracking_2801_ = lean_ctor_get_uint8(v_cfg_2794_, sizeof(void*)*1);
if (v_backtracking_2801_ == 0)
{
lean_object* v_toApplyRulesConfig_2802_; lean_object* v_toBacktrackConfig_2803_; lean_object* v_maxDepth_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_toApplyRulesConfig_2802_ = lean_ctor_get(v_cfg_2794_, 0);
v_toBacktrackConfig_2803_ = lean_ctor_get(v_toApplyRulesConfig_2802_, 0);
v_maxDepth_2804_ = lean_ctor_get(v_toBacktrackConfig_2803_, 0);
lean_inc(v_maxDepth_2804_);
v___x_2805_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2805_, 0, v_cfg_2794_);
lean_closure_set(v___x_2805_, 1, v_lemmas_2792_);
lean_closure_set(v___x_2805_, 2, v_ctx_2793_);
v___x_2806_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2805_, v_a_2795_, v_maxDepth_2804_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
return v___x_2806_;
}
else
{
lean_object* v_toApplyRulesConfig_2807_; lean_object* v_toBacktrackConfig_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_toApplyRulesConfig_2807_ = lean_ctor_get(v_cfg_2794_, 0);
v_toBacktrackConfig_2808_ = lean_ctor_get(v_toApplyRulesConfig_2807_, 0);
lean_inc_ref(v_toBacktrackConfig_2808_);
v___x_2809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2810_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2810_, 0, v_cfg_2794_);
lean_closure_set(v___x_2810_, 1, v_lemmas_2792_);
lean_closure_set(v___x_2810_, 2, v_ctx_2793_);
v___x_2811_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2808_, v___x_2809_, v___x_2810_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
return v___x_2811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2812_, lean_object* v_ctx_2813_, lean_object* v_cfg_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2812_, v_ctx_2813_, v_cfg_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2822_, v___y_2824_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v_mvarId_2829_);
return v_res_2835_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2836_, lean_object* v_x_2837_, lean_object* v_x_2838_){
_start:
{
uint8_t v___x_2839_; 
v___x_2839_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2837_, v_x_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2840_, lean_object* v_x_2841_, lean_object* v_x_2842_){
_start:
{
uint8_t v_res_2843_; lean_object* v_r_2844_; 
v_res_2843_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2840_, v_x_2841_, v_x_2842_);
lean_dec(v_x_2842_);
lean_dec_ref(v_x_2841_);
v_r_2844_ = lean_box(v_res_2843_);
return v_r_2844_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2845_, lean_object* v_x_2846_, size_t v_x_2847_, lean_object* v_x_2848_){
_start:
{
uint8_t v___x_2849_; 
v___x_2849_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2846_, v_x_2847_, v_x_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2850_, lean_object* v_x_2851_, lean_object* v_x_2852_, lean_object* v_x_2853_){
_start:
{
size_t v_x_2759__boxed_2854_; uint8_t v_res_2855_; lean_object* v_r_2856_; 
v_x_2759__boxed_2854_ = lean_unbox_usize(v_x_2852_);
lean_dec(v_x_2852_);
v_res_2855_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2850_, v_x_2851_, v_x_2759__boxed_2854_, v_x_2853_);
lean_dec(v_x_2853_);
lean_dec_ref(v_x_2851_);
v_r_2856_ = lean_box(v_res_2855_);
return v_r_2856_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2857_, lean_object* v_keys_2858_, lean_object* v_vals_2859_, lean_object* v_heq_2860_, lean_object* v_i_2861_, lean_object* v_k_2862_){
_start:
{
uint8_t v___x_2863_; 
v___x_2863_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2858_, v_i_2861_, v_k_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2864_, lean_object* v_keys_2865_, lean_object* v_vals_2866_, lean_object* v_heq_2867_, lean_object* v_i_2868_, lean_object* v_k_2869_){
_start:
{
uint8_t v_res_2870_; lean_object* v_r_2871_; 
v_res_2870_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2864_, v_keys_2865_, v_vals_2866_, v_heq_2867_, v_i_2868_, v_k_2869_);
lean_dec(v_k_2869_);
lean_dec_ref(v_vals_2866_);
lean_dec_ref(v_keys_2865_);
v_r_2871_ = lean_box(v_res_2870_);
return v_r_2871_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2874_ = l_Lean_stringToMessageData(v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec_ref(v_x_2883_);
return v_res_2889_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2892_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2893_ = l_Lean_Name_append(v___x_2892_, v___x_2891_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2894_, lean_object* v_lemmas_2895_, lean_object* v_ctx_2896_, lean_object* v_goals_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_cfg_2903_; lean_object* v___x_2904_; 
v_cfg_2903_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2894_);
lean_inc(v_goals_2897_);
lean_inc_ref(v_cfg_2903_);
lean_inc_ref(v_ctx_2896_);
lean_inc(v_lemmas_2895_);
v___x_2904_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2895_, v_ctx_2896_, v_cfg_2903_, v_goals_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_dec_ref(v_cfg_2903_);
lean_dec(v_goals_2897_);
lean_dec_ref(v_ctx_2896_);
lean_dec(v_lemmas_2895_);
return v___x_2904_;
}
else
{
lean_object* v_a_2905_; lean_object* v___f_2906_; uint8_t v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; uint8_t v___y_2914_; lean_object* v_a_2915_; uint8_t v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; uint8_t v___y_2934_; lean_object* v_a_2935_; uint8_t v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; uint8_t v___y_2944_; lean_object* v_a_2945_; uint8_t v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; uint8_t v___y_2961_; lean_object* v_a_2962_; lean_object* v___y_2965_; lean_object* v___y_2966_; uint8_t v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; uint8_t v___y_2971_; uint8_t v___y_3007_; uint8_t v___x_3060_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
v___f_2906_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_3060_ = l_Lean_Exception_isInterrupt(v_a_2905_);
if (v___x_3060_ == 0)
{
uint8_t v___x_3061_; 
v___x_3061_ = l_Lean_Exception_isRuntime(v_a_2905_);
v___y_3007_ = v___x_3061_;
goto v___jp_3006_;
}
else
{
lean_dec(v_a_2905_);
v___y_3007_ = v___x_3060_;
goto v___jp_3006_;
}
v___jp_2907_:
{
lean_object* v___x_2916_; double v___x_2917_; double v___x_2918_; double v___x_2919_; double v___x_2920_; double v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2916_ = lean_io_mono_nanos_now();
v___x_2917_ = lean_float_of_nat(v___y_2912_);
v___x_2918_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2919_ = lean_float_div(v___x_2917_, v___x_2918_);
v___x_2920_ = lean_float_of_nat(v___x_2916_);
v___x_2921_ = lean_float_div(v___x_2920_, v___x_2918_);
v___x_2922_ = lean_box_float(v___x_2919_);
v___x_2923_ = lean_box_float(v___x_2921_);
v___x_2924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2922_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v_a_2915_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
lean_inc_ref(v___y_2910_);
lean_inc(v___y_2911_);
v___x_2926_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2911_, v___y_2914_, v___y_2910_, v___y_2909_, v___y_2908_, v___y_2913_, v___f_2906_, v___x_2925_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
return v___x_2926_;
}
v___jp_2927_:
{
lean_object* v___x_2936_; 
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v_a_2935_);
v___y_2908_ = v___y_2928_;
v___y_2909_ = v___y_2929_;
v___y_2910_ = v___y_2930_;
v___y_2911_ = v___y_2931_;
v___y_2912_ = v___y_2932_;
v___y_2913_ = v___y_2933_;
v___y_2914_ = v___y_2934_;
v_a_2915_ = v___x_2936_;
goto v___jp_2907_;
}
v___jp_2937_:
{
lean_object* v___x_2946_; double v___x_2947_; double v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2946_ = lean_io_get_num_heartbeats();
v___x_2947_ = lean_float_of_nat(v___y_2939_);
v___x_2948_ = lean_float_of_nat(v___x_2946_);
v___x_2949_ = lean_box_float(v___x_2947_);
v___x_2950_ = lean_box_float(v___x_2948_);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2949_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v_a_2945_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
lean_inc_ref(v___y_2941_);
lean_inc(v___y_2942_);
v___x_2953_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2942_, v___y_2944_, v___y_2941_, v___y_2940_, v___y_2938_, v___y_2943_, v___f_2906_, v___x_2952_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
return v___x_2953_;
}
v___jp_2954_:
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v_a_2962_);
v___y_2938_ = v___y_2955_;
v___y_2939_ = v___y_2956_;
v___y_2940_ = v___y_2957_;
v___y_2941_ = v___y_2958_;
v___y_2942_ = v___y_2959_;
v___y_2943_ = v___y_2960_;
v___y_2944_ = v___y_2961_;
v_a_2945_ = v___x_2963_;
goto v___jp_2937_;
}
v___jp_2964_:
{
lean_object* v___x_2972_; lean_object* v_a_2973_; lean_object* v___x_2974_; uint8_t v___x_2975_; 
v___x_2972_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2901_);
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref(v___x_2972_);
v___x_2974_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2975_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2968_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = lean_io_mono_nanos_now();
v___x_2977_ = l_Lean_MVarId_exfalso(v___y_2966_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref(v___x_2977_);
v___x_2979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2979_, 0, v_a_2978_);
lean_ctor_set(v___x_2979_, 1, v___y_2965_);
v___x_2980_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2895_, v_ctx_2896_, v_cfg_2903_, v___x_2979_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2980_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2980_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set_tag(v___x_2983_, 1);
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
v___y_2908_ = v___y_2967_;
v___y_2909_ = v___y_2968_;
v___y_2910_ = v___y_2969_;
v___y_2911_ = v___y_2970_;
v___y_2912_ = v___x_2976_;
v___y_2913_ = v_a_2973_;
v___y_2914_ = v___y_2971_;
v_a_2915_ = v___x_2986_;
goto v___jp_2907_;
}
}
}
else
{
lean_object* v_a_2989_; 
v_a_2989_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2989_);
lean_dec_ref(v___x_2980_);
v___y_2928_ = v___y_2967_;
v___y_2929_ = v___y_2968_;
v___y_2930_ = v___y_2969_;
v___y_2931_ = v___y_2970_;
v___y_2932_ = v___x_2976_;
v___y_2933_ = v_a_2973_;
v___y_2934_ = v___y_2971_;
v_a_2935_ = v_a_2989_;
goto v___jp_2927_;
}
}
else
{
lean_object* v_a_2990_; 
lean_dec(v___y_2965_);
lean_dec_ref(v_cfg_2903_);
lean_dec_ref(v_ctx_2896_);
lean_dec(v_lemmas_2895_);
v_a_2990_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2990_);
lean_dec_ref(v___x_2977_);
v___y_2928_ = v___y_2967_;
v___y_2929_ = v___y_2968_;
v___y_2930_ = v___y_2969_;
v___y_2931_ = v___y_2970_;
v___y_2932_ = v___x_2976_;
v___y_2933_ = v_a_2973_;
v___y_2934_ = v___y_2971_;
v_a_2935_ = v_a_2990_;
goto v___jp_2927_;
}
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_io_get_num_heartbeats();
v___x_2992_ = l_Lean_MVarId_exfalso(v___y_2966_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref(v___x_2992_);
v___x_2994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2994_, 0, v_a_2993_);
lean_ctor_set(v___x_2994_, 1, v___y_2965_);
v___x_2995_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2895_, v_ctx_2896_, v_cfg_2903_, v___x_2994_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2995_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
lean_ctor_set_tag(v___x_2998_, 1);
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
v___y_2938_ = v___y_2967_;
v___y_2939_ = v___x_2991_;
v___y_2940_ = v___y_2968_;
v___y_2941_ = v___y_2969_;
v___y_2942_ = v___y_2970_;
v___y_2943_ = v_a_2973_;
v___y_2944_ = v___y_2971_;
v_a_2945_ = v___x_3001_;
goto v___jp_2937_;
}
}
}
else
{
lean_object* v_a_3004_; 
v_a_3004_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_2995_);
v___y_2955_ = v___y_2967_;
v___y_2956_ = v___x_2991_;
v___y_2957_ = v___y_2968_;
v___y_2958_ = v___y_2969_;
v___y_2959_ = v___y_2970_;
v___y_2960_ = v_a_2973_;
v___y_2961_ = v___y_2971_;
v_a_2962_ = v_a_3004_;
goto v___jp_2954_;
}
}
else
{
lean_object* v_a_3005_; 
lean_dec(v___y_2965_);
lean_dec_ref(v_cfg_2903_);
lean_dec_ref(v_ctx_2896_);
lean_dec(v_lemmas_2895_);
v_a_3005_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_3005_);
lean_dec_ref(v___x_2992_);
v___y_2955_ = v___y_2967_;
v___y_2956_ = v___x_2991_;
v___y_2957_ = v___y_2968_;
v___y_2958_ = v___y_2969_;
v___y_2959_ = v___y_2970_;
v___y_2960_ = v_a_2973_;
v___y_2961_ = v___y_2971_;
v_a_2962_ = v_a_3005_;
goto v___jp_2954_;
}
}
}
v___jp_3006_:
{
if (v___y_3007_ == 0)
{
if (lean_obj_tag(v_goals_2897_) == 1)
{
lean_object* v_tail_3008_; 
v_tail_3008_ = lean_ctor_get(v_goals_2897_, 1);
lean_inc(v_tail_3008_);
if (lean_obj_tag(v_tail_3008_) == 0)
{
lean_object* v_toApplyRulesConfig_3009_; uint8_t v_exfalso_3010_; 
v_toApplyRulesConfig_3009_ = lean_ctor_get(v_cfg_2903_, 0);
lean_inc_ref(v_toApplyRulesConfig_3009_);
v_exfalso_3010_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3009_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_3009_);
if (v_exfalso_3010_ == 1)
{
lean_object* v_options_3011_; uint8_t v_hasTrace_3012_; 
lean_dec_ref(v___x_2904_);
v_options_3011_ = lean_ctor_get(v_a_2900_, 2);
v_hasTrace_3012_ = lean_ctor_get_uint8(v_options_3011_, sizeof(void*)*1);
if (v_hasTrace_3012_ == 0)
{
lean_object* v_head_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3031_; 
v_head_3013_ = lean_ctor_get(v_goals_2897_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v_goals_2897_);
if (v_isSharedCheck_3031_ == 0)
{
lean_object* v_unused_3032_; 
v_unused_3032_ = lean_ctor_get(v_goals_2897_, 1);
lean_dec(v_unused_3032_);
v___x_3015_ = v_goals_2897_;
v_isShared_3016_ = v_isSharedCheck_3031_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_head_3013_);
lean_dec(v_goals_2897_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3031_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Lean_MVarId_exfalso(v_head_3013_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3020_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref(v___x_3017_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v_a_3018_);
v___x_3020_ = v___x_3015_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3018_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_tail_3008_);
v___x_3020_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; 
v___x_3021_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2895_, v_ctx_2896_, v_cfg_2903_, v___x_3020_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
return v___x_3021_;
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_del_object(v___x_3015_);
lean_dec_ref(v_cfg_2903_);
lean_dec_ref(v_ctx_2896_);
lean_dec(v_lemmas_2895_);
v_a_3023_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3017_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3017_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
else
{
lean_object* v_head_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3058_; 
v_head_3033_ = lean_ctor_get(v_goals_2897_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_goals_2897_);
if (v_isSharedCheck_3058_ == 0)
{
lean_object* v_unused_3059_; 
v_unused_3059_ = lean_ctor_get(v_goals_2897_, 1);
lean_dec(v_unused_3059_);
v___x_3035_ = v_goals_2897_;
v_isShared_3036_ = v_isSharedCheck_3058_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_head_3033_);
lean_dec(v_goals_2897_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3058_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v_inheritedTraceOptions_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
v_inheritedTraceOptions_3037_ = lean_ctor_get(v_a_2900_, 13);
v___x_3038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_3039_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_3040_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_3041_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3037_, v_options_3011_, v___x_3040_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = l_Lean_trace_profiler;
v___x_3043_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_3011_, v___x_3042_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_MVarId_exfalso(v_head_3033_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref(v___x_3044_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 0, v_a_3045_);
v___x_3047_ = v___x_3035_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3045_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_tail_3008_);
v___x_3047_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3048_; 
v___x_3048_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2895_, v_ctx_2896_, v_cfg_2903_, v___x_3047_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
return v___x_3048_;
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_del_object(v___x_3035_);
lean_dec_ref(v_cfg_2903_);
lean_dec_ref(v_ctx_2896_);
lean_dec(v_lemmas_2895_);
v_a_3050_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3044_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3044_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
else
{
lean_del_object(v___x_3035_);
v___y_2965_ = v_tail_3008_;
v___y_2966_ = v_head_3033_;
v___y_2967_ = v___x_3041_;
v___y_2968_ = v_options_3011_;
v___y_2969_ = v___x_3039_;
v___y_2970_ = v___x_3038_;
v___y_2971_ = v_exfalso_3010_;
goto v___jp_2964_;
}
}
else
{
lean_del_object(v___x_3035_);
v___y_2965_ = v_tail_3008_;
v___y_2966_ = v_head_3033_;
v___y_2967_ = v___x_3041_;
v___y_2968_ = v_options_3011_;
v___y_2969_ = v___x_3039_;
v___y_2970_ = v___x_3038_;
v___y_2971_ = v_exfalso_3010_;
goto v___jp_2964_;
}
}
}
}
else
{
lean_dec_ref(v_goals_2897_);
lean_dec_ref(v_cfg_2903_);
lean_dec_ref(v_ctx_2896_);
lean_dec(v_lemmas_2895_);
return v___x_2904_;
}
}
else
{
lean_dec_ref(v_goals_2897_);
lean_dec(v_tail_3008_);
lean_dec_ref(v_cfg_2903_);
lean_dec_ref(v_ctx_2896_);
lean_dec(v_lemmas_2895_);
return v___x_2904_;
}
}
else
{
lean_dec_ref(v_cfg_2903_);
lean_dec(v_goals_2897_);
lean_dec_ref(v_ctx_2896_);
lean_dec(v_lemmas_2895_);
return v___x_2904_;
}
}
else
{
lean_dec_ref(v_cfg_2903_);
lean_dec(v_goals_2897_);
lean_dec_ref(v_ctx_2896_);
lean_dec(v_lemmas_2895_);
return v___x_2904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_3062_, lean_object* v_lemmas_3063_, lean_object* v_ctx_3064_, lean_object* v_goals_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_3062_, v_lemmas_3063_, v_ctx_3064_, v_goals_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_3072_, lean_object* v_x_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
if (lean_obj_tag(v_x_3072_) == 0)
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = l_List_reverse___redArg(v_x_3073_);
v___x_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
return v___x_3080_;
}
else
{
lean_object* v_head_3081_; lean_object* v_tail_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3105_; 
v_head_3081_ = lean_ctor_get(v_x_3072_, 0);
v_tail_3082_ = lean_ctor_get(v_x_3072_, 1);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_x_3072_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3084_ = v_x_3072_;
v_isShared_3085_ = v_isSharedCheck_3105_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_tail_3082_);
lean_inc(v_head_3081_);
lean_dec(v_x_3072_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3105_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; 
v___x_3086_ = l_Lean_Expr_applySymm(v_head_3081_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3089_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref(v___x_3086_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 1, v_x_3073_);
lean_ctor_set(v___x_3084_, 0, v_a_3087_);
v___x_3089_ = v___x_3084_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3087_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_x_3073_);
v___x_3089_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
v_x_3072_ = v_tail_3082_;
v_x_3073_ = v___x_3089_;
goto _start;
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3104_; 
lean_del_object(v___x_3084_);
v_a_3092_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3094_ = v___x_3086_;
v_isShared_3095_ = v_isSharedCheck_3104_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3086_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3104_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
uint8_t v___y_3097_; uint8_t v___x_3102_; 
v___x_3102_ = l_Lean_Exception_isInterrupt(v_a_3092_);
if (v___x_3102_ == 0)
{
uint8_t v___x_3103_; 
lean_inc(v_a_3092_);
v___x_3103_ = l_Lean_Exception_isRuntime(v_a_3092_);
v___y_3097_ = v___x_3103_;
goto v___jp_3096_;
}
else
{
v___y_3097_ = v___x_3102_;
goto v___jp_3096_;
}
v___jp_3096_:
{
if (v___y_3097_ == 0)
{
lean_del_object(v___x_3094_);
lean_dec(v_a_3092_);
v_x_3072_ = v_tail_3082_;
goto _start;
}
else
{
lean_object* v___x_3100_; 
lean_dec(v_tail_3082_);
lean_dec(v_x_3073_);
if (v_isShared_3095_ == 0)
{
v___x_3100_ = v___x_3094_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3092_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_3106_, lean_object* v_x_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_3106_, v_x_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_3114_, lean_object* v_hyps_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
if (v_symm_3114_ == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_hyps_3115_);
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = lean_box(0);
lean_inc(v_hyps_3115_);
v___x_3123_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_3115_, v___x_3122_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3132_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3126_ = v___x_3123_;
v_isShared_3127_ = v_isSharedCheck_3132_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3132_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; lean_object* v___x_3130_; 
v___x_3128_ = l_List_appendTR___redArg(v_hyps_3115_, v_a_3124_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v___x_3128_);
v___x_3130_ = v___x_3126_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
else
{
lean_dec(v_hyps_3115_);
return v___x_3123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3133_, lean_object* v_hyps_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_){
_start:
{
uint8_t v_symm_boxed_3140_; lean_object* v_res_3141_; 
v_symm_boxed_3140_ = lean_unbox(v_symm_3133_);
v_res_3141_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3140_, v_hyps_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_);
lean_dec(v_a_3138_);
lean_dec_ref(v_a_3137_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3142_, size_t v_sz_3143_, size_t v_i_3144_, lean_object* v_b_3145_){
_start:
{
uint8_t v___x_3147_; 
v___x_3147_ = lean_usize_dec_lt(v_i_3144_, v_sz_3143_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_b_3145_);
return v___x_3148_;
}
else
{
lean_object* v_snd_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3167_; 
v_snd_3149_ = lean_ctor_get(v_b_3145_, 1);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_b_3145_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v_b_3145_, 0);
lean_dec(v_unused_3168_);
v___x_3151_ = v_b_3145_;
v_isShared_3152_ = v_isSharedCheck_3167_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_snd_3149_);
lean_dec(v_b_3145_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3167_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v_a_3155_; lean_object* v_a_3162_; 
v___x_3153_ = lean_box(0);
v_a_3162_ = lean_array_uget_borrowed(v_as_3142_, v_i_3144_);
if (lean_obj_tag(v_a_3162_) == 0)
{
v_a_3155_ = v_snd_3149_;
goto v___jp_3154_;
}
else
{
lean_object* v_val_3163_; uint8_t v___x_3164_; 
v_val_3163_ = lean_ctor_get(v_a_3162_, 0);
v___x_3164_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3163_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_inc(v_val_3163_);
v___x_3165_ = l_Lean_LocalDecl_toExpr(v_val_3163_);
v___x_3166_ = lean_array_push(v_snd_3149_, v___x_3165_);
v_a_3155_ = v___x_3166_;
goto v___jp_3154_;
}
else
{
v_a_3155_ = v_snd_3149_;
goto v___jp_3154_;
}
}
v___jp_3154_:
{
lean_object* v___x_3157_; 
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 1, v_a_3155_);
lean_ctor_set(v___x_3151_, 0, v___x_3153_);
v___x_3157_ = v___x_3151_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3153_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v_a_3155_);
v___x_3157_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
size_t v___x_3158_; size_t v___x_3159_; 
v___x_3158_ = ((size_t)1ULL);
v___x_3159_ = lean_usize_add(v_i_3144_, v___x_3158_);
v_i_3144_ = v___x_3159_;
v_b_3145_ = v___x_3157_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3169_, lean_object* v_sz_3170_, lean_object* v_i_3171_, lean_object* v_b_3172_, lean_object* v___y_3173_){
_start:
{
size_t v_sz_boxed_3174_; size_t v_i_boxed_3175_; lean_object* v_res_3176_; 
v_sz_boxed_3174_ = lean_unbox_usize(v_sz_3170_);
lean_dec(v_sz_3170_);
v_i_boxed_3175_ = lean_unbox_usize(v_i_3171_);
lean_dec(v_i_3171_);
v_res_3176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3169_, v_sz_boxed_3174_, v_i_boxed_3175_, v_b_3172_);
lean_dec_ref(v_as_3169_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3177_, size_t v_sz_3178_, size_t v_i_3179_, lean_object* v_b_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
uint8_t v___x_3188_; 
v___x_3188_ = lean_usize_dec_lt(v_i_3179_, v_sz_3178_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; 
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v_b_3180_);
return v___x_3189_;
}
else
{
lean_object* v_snd_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3208_; 
v_snd_3190_ = lean_ctor_get(v_b_3180_, 1);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_b_3180_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v_b_3180_, 0);
lean_dec(v_unused_3209_);
v___x_3192_ = v_b_3180_;
v_isShared_3193_ = v_isSharedCheck_3208_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_snd_3190_);
lean_dec(v_b_3180_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3208_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3194_; lean_object* v_a_3196_; lean_object* v_a_3203_; 
v___x_3194_ = lean_box(0);
v_a_3203_ = lean_array_uget_borrowed(v_as_3177_, v_i_3179_);
if (lean_obj_tag(v_a_3203_) == 0)
{
v_a_3196_ = v_snd_3190_;
goto v___jp_3195_;
}
else
{
lean_object* v_val_3204_; uint8_t v___x_3205_; 
v_val_3204_ = lean_ctor_get(v_a_3203_, 0);
v___x_3205_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3204_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
lean_inc(v_val_3204_);
v___x_3206_ = l_Lean_LocalDecl_toExpr(v_val_3204_);
v___x_3207_ = lean_array_push(v_snd_3190_, v___x_3206_);
v_a_3196_ = v___x_3207_;
goto v___jp_3195_;
}
else
{
v_a_3196_ = v_snd_3190_;
goto v___jp_3195_;
}
}
v___jp_3195_:
{
lean_object* v___x_3198_; 
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 1, v_a_3196_);
lean_ctor_set(v___x_3192_, 0, v___x_3194_);
v___x_3198_ = v___x_3192_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3194_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v_a_3196_);
v___x_3198_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
size_t v___x_3199_; size_t v___x_3200_; lean_object* v___x_3201_; 
v___x_3199_ = ((size_t)1ULL);
v___x_3200_ = lean_usize_add(v_i_3179_, v___x_3199_);
v___x_3201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3177_, v_sz_3178_, v___x_3200_, v___x_3198_);
return v___x_3201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3210_, lean_object* v_sz_3211_, lean_object* v_i_3212_, lean_object* v_b_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
size_t v_sz_boxed_3221_; size_t v_i_boxed_3222_; lean_object* v_res_3223_; 
v_sz_boxed_3221_ = lean_unbox_usize(v_sz_3211_);
lean_dec(v_sz_3211_);
v_i_boxed_3222_ = lean_unbox_usize(v_i_3212_);
lean_dec(v_i_3212_);
v_res_3223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3210_, v_sz_boxed_3221_, v_i_boxed_3222_, v_b_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec_ref(v_as_3210_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3224_, size_t v_sz_3225_, size_t v_i_3226_, lean_object* v_b_3227_){
_start:
{
uint8_t v___x_3229_; 
v___x_3229_ = lean_usize_dec_lt(v_i_3226_, v_sz_3225_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3230_, 0, v_b_3227_);
return v___x_3230_;
}
else
{
lean_object* v_snd_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3249_; 
v_snd_3231_ = lean_ctor_get(v_b_3227_, 1);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_b_3227_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v_b_3227_, 0);
lean_dec(v_unused_3250_);
v___x_3233_ = v_b_3227_;
v_isShared_3234_ = v_isSharedCheck_3249_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_snd_3231_);
lean_dec(v_b_3227_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3249_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; lean_object* v_a_3237_; lean_object* v_a_3244_; 
v___x_3235_ = lean_box(0);
v_a_3244_ = lean_array_uget_borrowed(v_as_3224_, v_i_3226_);
if (lean_obj_tag(v_a_3244_) == 0)
{
v_a_3237_ = v_snd_3231_;
goto v___jp_3236_;
}
else
{
lean_object* v_val_3245_; uint8_t v___x_3246_; 
v_val_3245_ = lean_ctor_get(v_a_3244_, 0);
v___x_3246_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3245_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_inc(v_val_3245_);
v___x_3247_ = l_Lean_LocalDecl_toExpr(v_val_3245_);
v___x_3248_ = lean_array_push(v_snd_3231_, v___x_3247_);
v_a_3237_ = v___x_3248_;
goto v___jp_3236_;
}
else
{
v_a_3237_ = v_snd_3231_;
goto v___jp_3236_;
}
}
v___jp_3236_:
{
lean_object* v___x_3239_; 
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v_a_3237_);
lean_ctor_set(v___x_3233_, 0, v___x_3235_);
v___x_3239_ = v___x_3233_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v_a_3237_);
v___x_3239_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
size_t v___x_3240_; size_t v___x_3241_; 
v___x_3240_ = ((size_t)1ULL);
v___x_3241_ = lean_usize_add(v_i_3226_, v___x_3240_);
v_i_3226_ = v___x_3241_;
v_b_3227_ = v___x_3239_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3251_, lean_object* v_sz_3252_, lean_object* v_i_3253_, lean_object* v_b_3254_, lean_object* v___y_3255_){
_start:
{
size_t v_sz_boxed_3256_; size_t v_i_boxed_3257_; lean_object* v_res_3258_; 
v_sz_boxed_3256_ = lean_unbox_usize(v_sz_3252_);
lean_dec(v_sz_3252_);
v_i_boxed_3257_ = lean_unbox_usize(v_i_3253_);
lean_dec(v_i_3253_);
v_res_3258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3251_, v_sz_boxed_3256_, v_i_boxed_3257_, v_b_3254_);
lean_dec_ref(v_as_3251_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3259_, size_t v_sz_3260_, size_t v_i_3261_, lean_object* v_b_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
uint8_t v___x_3270_; 
v___x_3270_ = lean_usize_dec_lt(v_i_3261_, v_sz_3260_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_b_3262_);
return v___x_3271_;
}
else
{
lean_object* v_snd_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3290_; 
v_snd_3272_ = lean_ctor_get(v_b_3262_, 1);
v_isSharedCheck_3290_ = !lean_is_exclusive(v_b_3262_);
if (v_isSharedCheck_3290_ == 0)
{
lean_object* v_unused_3291_; 
v_unused_3291_ = lean_ctor_get(v_b_3262_, 0);
lean_dec(v_unused_3291_);
v___x_3274_ = v_b_3262_;
v_isShared_3275_ = v_isSharedCheck_3290_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_snd_3272_);
lean_dec(v_b_3262_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3290_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v_a_3278_; lean_object* v_a_3285_; 
v___x_3276_ = lean_box(0);
v_a_3285_ = lean_array_uget_borrowed(v_as_3259_, v_i_3261_);
if (lean_obj_tag(v_a_3285_) == 0)
{
v_a_3278_ = v_snd_3272_;
goto v___jp_3277_;
}
else
{
lean_object* v_val_3286_; uint8_t v___x_3287_; 
v_val_3286_ = lean_ctor_get(v_a_3285_, 0);
v___x_3287_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3286_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
lean_inc(v_val_3286_);
v___x_3288_ = l_Lean_LocalDecl_toExpr(v_val_3286_);
v___x_3289_ = lean_array_push(v_snd_3272_, v___x_3288_);
v_a_3278_ = v___x_3289_;
goto v___jp_3277_;
}
else
{
v_a_3278_ = v_snd_3272_;
goto v___jp_3277_;
}
}
v___jp_3277_:
{
lean_object* v___x_3280_; 
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 1, v_a_3278_);
lean_ctor_set(v___x_3274_, 0, v___x_3276_);
v___x_3280_ = v___x_3274_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_a_3278_);
v___x_3280_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
size_t v___x_3281_; size_t v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = ((size_t)1ULL);
v___x_3282_ = lean_usize_add(v_i_3261_, v___x_3281_);
v___x_3283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3259_, v_sz_3260_, v___x_3282_, v___x_3280_);
return v___x_3283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3292_, lean_object* v_sz_3293_, lean_object* v_i_3294_, lean_object* v_b_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
size_t v_sz_boxed_3303_; size_t v_i_boxed_3304_; lean_object* v_res_3305_; 
v_sz_boxed_3303_ = lean_unbox_usize(v_sz_3293_);
lean_dec(v_sz_3293_);
v_i_boxed_3304_ = lean_unbox_usize(v_i_3294_);
lean_dec(v_i_3294_);
v_res_3305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3292_, v_sz_boxed_3303_, v_i_boxed_3304_, v_b_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v_as_3292_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3306_, lean_object* v_n_3307_, lean_object* v_b_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
if (lean_obj_tag(v_n_3307_) == 0)
{
lean_object* v_cs_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; size_t v_sz_3319_; size_t v___x_3320_; lean_object* v___x_3321_; 
v_cs_3316_ = lean_ctor_get(v_n_3307_, 0);
v___x_3317_ = lean_box(0);
v___x_3318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
lean_ctor_set(v___x_3318_, 1, v_b_3308_);
v_sz_3319_ = lean_array_size(v_cs_3316_);
v___x_3320_ = ((size_t)0ULL);
v___x_3321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3306_, v_cs_3316_, v_sz_3319_, v___x_3320_, v___x_3318_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3336_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3336_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3336_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v_fst_3326_; 
v_fst_3326_ = lean_ctor_get(v_a_3322_, 0);
if (lean_obj_tag(v_fst_3326_) == 0)
{
lean_object* v_snd_3327_; lean_object* v___x_3328_; lean_object* v___x_3330_; 
v_snd_3327_ = lean_ctor_get(v_a_3322_, 1);
lean_inc(v_snd_3327_);
lean_dec(v_a_3322_);
v___x_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_snd_3327_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3328_);
v___x_3330_ = v___x_3324_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3328_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
else
{
lean_object* v_val_3332_; lean_object* v___x_3334_; 
lean_inc_ref(v_fst_3326_);
lean_dec(v_a_3322_);
v_val_3332_ = lean_ctor_get(v_fst_3326_, 0);
lean_inc(v_val_3332_);
lean_dec_ref(v_fst_3326_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v_val_3332_);
v___x_3334_ = v___x_3324_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_val_3332_);
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
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
v_a_3337_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3321_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3321_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
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
lean_object* v_vs_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; size_t v_sz_3348_; size_t v___x_3349_; lean_object* v___x_3350_; 
v_vs_3345_ = lean_ctor_get(v_n_3307_, 0);
v___x_3346_ = lean_box(0);
v___x_3347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
lean_ctor_set(v___x_3347_, 1, v_b_3308_);
v_sz_3348_ = lean_array_size(v_vs_3345_);
v___x_3349_ = ((size_t)0ULL);
v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3345_, v_sz_3348_, v___x_3349_, v___x_3347_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3365_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3353_ = v___x_3350_;
v_isShared_3354_ = v_isSharedCheck_3365_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3365_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v_fst_3355_; 
v_fst_3355_ = lean_ctor_get(v_a_3351_, 0);
if (lean_obj_tag(v_fst_3355_) == 0)
{
lean_object* v_snd_3356_; lean_object* v___x_3357_; lean_object* v___x_3359_; 
v_snd_3356_ = lean_ctor_get(v_a_3351_, 1);
lean_inc(v_snd_3356_);
lean_dec(v_a_3351_);
v___x_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3357_, 0, v_snd_3356_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v___x_3357_);
v___x_3359_ = v___x_3353_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
else
{
lean_object* v_val_3361_; lean_object* v___x_3363_; 
lean_inc_ref(v_fst_3355_);
lean_dec(v_a_3351_);
v_val_3361_ = lean_ctor_get(v_fst_3355_, 0);
lean_inc(v_val_3361_);
lean_dec_ref(v_fst_3355_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v_val_3361_);
v___x_3363_ = v___x_3353_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_val_3361_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
v_a_3366_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3350_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3350_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3374_, lean_object* v_as_3375_, size_t v_sz_3376_, size_t v_i_3377_, lean_object* v_b_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
uint8_t v___x_3386_; 
v___x_3386_ = lean_usize_dec_lt(v_i_3377_, v_sz_3376_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; 
v___x_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3387_, 0, v_b_3378_);
return v___x_3387_;
}
else
{
lean_object* v_snd_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3422_; 
v_snd_3388_ = lean_ctor_get(v_b_3378_, 1);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_b_3378_);
if (v_isSharedCheck_3422_ == 0)
{
lean_object* v_unused_3423_; 
v_unused_3423_ = lean_ctor_get(v_b_3378_, 0);
lean_dec(v_unused_3423_);
v___x_3390_ = v_b_3378_;
v_isShared_3391_ = v_isSharedCheck_3422_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_snd_3388_);
lean_dec(v_b_3378_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3422_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v_a_3392_; lean_object* v___x_3393_; 
v_a_3392_ = lean_array_uget_borrowed(v_as_3375_, v_i_3377_);
lean_inc(v_snd_3388_);
v___x_3393_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3374_, v_a_3392_, v_snd_3388_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3413_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3413_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3413_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
if (lean_obj_tag(v_a_3394_) == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3400_; 
v___x_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3398_, 0, v_a_3394_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3398_);
v___x_3400_ = v___x_3390_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_snd_3388_);
v___x_3400_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3402_; 
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3400_);
v___x_3402_ = v___x_3396_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
lean_del_object(v___x_3396_);
lean_dec(v_snd_3388_);
v_a_3405_ = lean_ctor_get(v_a_3394_, 0);
lean_inc(v_a_3405_);
lean_dec_ref(v_a_3394_);
v___x_3406_ = lean_box(0);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 1, v_a_3405_);
lean_ctor_set(v___x_3390_, 0, v___x_3406_);
v___x_3408_ = v___x_3390_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3406_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_a_3405_);
v___x_3408_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
size_t v___x_3409_; size_t v___x_3410_; 
v___x_3409_ = ((size_t)1ULL);
v___x_3410_ = lean_usize_add(v_i_3377_, v___x_3409_);
v_i_3377_ = v___x_3410_;
v_b_3378_ = v___x_3408_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_del_object(v___x_3390_);
lean_dec(v_snd_3388_);
v_a_3414_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3393_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3393_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3424_, lean_object* v_as_3425_, lean_object* v_sz_3426_, lean_object* v_i_3427_, lean_object* v_b_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
size_t v_sz_boxed_3436_; size_t v_i_boxed_3437_; lean_object* v_res_3438_; 
v_sz_boxed_3436_ = lean_unbox_usize(v_sz_3426_);
lean_dec(v_sz_3426_);
v_i_boxed_3437_ = lean_unbox_usize(v_i_3427_);
lean_dec(v_i_3427_);
v_res_3438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3424_, v_as_3425_, v_sz_boxed_3436_, v_i_boxed_3437_, v_b_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec_ref(v_as_3425_);
lean_dec_ref(v_init_3424_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3439_, lean_object* v_n_3440_, lean_object* v_b_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3439_, v_n_3440_, v_b_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v_n_3440_);
lean_dec_ref(v_init_3439_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3450_, lean_object* v_init_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_root_3459_; lean_object* v_tail_3460_; lean_object* v___x_3461_; 
v_root_3459_ = lean_ctor_get(v_t_3450_, 0);
v_tail_3460_ = lean_ctor_get(v_t_3450_, 1);
lean_inc_ref(v_init_3451_);
v___x_3461_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3451_, v_root_3459_, v_init_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec_ref(v_init_3451_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3498_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3464_ = v___x_3461_;
v_isShared_3465_ = v_isSharedCheck_3498_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3498_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
if (lean_obj_tag(v_a_3462_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3468_; 
v_a_3466_ = lean_ctor_get(v_a_3462_, 0);
lean_inc(v_a_3466_);
lean_dec_ref(v_a_3462_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v_a_3466_);
v___x_3468_ = v___x_3464_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3466_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; size_t v_sz_3473_; size_t v___x_3474_; lean_object* v___x_3475_; 
lean_del_object(v___x_3464_);
v_a_3470_ = lean_ctor_get(v_a_3462_, 0);
lean_inc(v_a_3470_);
lean_dec_ref(v_a_3462_);
v___x_3471_ = lean_box(0);
v___x_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
lean_ctor_set(v___x_3472_, 1, v_a_3470_);
v_sz_3473_ = lean_array_size(v_tail_3460_);
v___x_3474_ = ((size_t)0ULL);
v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3460_, v_sz_3473_, v___x_3474_, v___x_3472_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3489_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3478_ = v___x_3475_;
v_isShared_3479_ = v_isSharedCheck_3489_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3475_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3489_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v_fst_3480_; 
v_fst_3480_ = lean_ctor_get(v_a_3476_, 0);
if (lean_obj_tag(v_fst_3480_) == 0)
{
lean_object* v_snd_3481_; lean_object* v___x_3483_; 
v_snd_3481_ = lean_ctor_get(v_a_3476_, 1);
lean_inc(v_snd_3481_);
lean_dec(v_a_3476_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v_snd_3481_);
v___x_3483_ = v___x_3478_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_snd_3481_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
else
{
lean_object* v_val_3485_; lean_object* v___x_3487_; 
lean_inc_ref(v_fst_3480_);
lean_dec(v_a_3476_);
v_val_3485_ = lean_ctor_get(v_fst_3480_, 0);
lean_inc(v_val_3485_);
lean_dec_ref(v_fst_3480_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v_val_3485_);
v___x_3487_ = v___x_3478_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_val_3485_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
v_a_3490_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3475_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3475_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
}
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
v_a_3499_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3461_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3461_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3507_, lean_object* v_init_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3507_, v_init_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v_t_3507_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v_lctx_3526_; lean_object* v_decls_3527_; lean_object* v_hs_3528_; lean_object* v___x_3529_; 
v_lctx_3526_ = lean_ctor_get(v___y_3521_, 2);
v_decls_3527_ = lean_ctor_get(v_lctx_3526_, 1);
v_hs_3528_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3529_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3527_, v_hs_3528_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3538_, lean_object* v_cfg_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
if (v_only_3538_ == 0)
{
lean_object* v___x_3547_; 
v___x_3547_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_toApplyRulesConfig_3548_; lean_object* v_a_3549_; uint8_t v_symm_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v_toApplyRulesConfig_3548_ = lean_ctor_get(v_cfg_3539_, 0);
v_a_3549_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3549_);
lean_dec_ref(v___x_3547_);
v_symm_3550_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3548_, sizeof(void*)*2 + 1);
v___x_3551_ = lean_array_to_list(v_a_3549_);
v___x_3552_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3550_, v___x_3551_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
return v___x_3552_;
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
v_a_3553_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3547_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3547_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = lean_box(0);
v___x_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
return v___x_3562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3563_, lean_object* v_cfg_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
uint8_t v_only_boxed_3572_; lean_object* v_res_3573_; 
v_only_boxed_3572_ = lean_unbox(v_only_3563_);
v_res_3573_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3572_, v_cfg_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec_ref(v_cfg_3564_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3574_, lean_object* v_lemmas_3575_, uint8_t v_only_3576_, lean_object* v_g_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v_toApplyRulesConfig_3583_; uint8_t v_intro_3584_; uint8_t v_constructor_3585_; uint8_t v_suggestions_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3599_; 
v_toApplyRulesConfig_3583_ = lean_ctor_get(v_cfg_3574_, 0);
v_intro_3584_ = lean_ctor_get_uint8(v_cfg_3574_, sizeof(void*)*1 + 1);
v_constructor_3585_ = lean_ctor_get_uint8(v_cfg_3574_, sizeof(void*)*1 + 2);
v_suggestions_3586_ = lean_ctor_get_uint8(v_cfg_3574_, sizeof(void*)*1 + 3);
v_isSharedCheck_3599_ = !lean_is_exclusive(v_cfg_3574_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3588_ = v_cfg_3574_;
v_isShared_3589_ = v_isSharedCheck_3599_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_toApplyRulesConfig_3583_);
lean_dec(v_cfg_3574_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3599_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v_ctx_3591_; uint8_t v___x_3592_; lean_object* v___x_3594_; 
v___x_3590_ = lean_box(v_only_3576_);
v_ctx_3591_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3591_, 0, v___x_3590_);
v___x_3592_ = 0;
if (v_isShared_3589_ == 0)
{
v___x_3594_ = v___x_3588_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_toApplyRulesConfig_3583_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, sizeof(void*)*1 + 1, v_intro_3584_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, sizeof(void*)*1 + 2, v_constructor_3585_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, sizeof(void*)*1 + 3, v_suggestions_3586_);
v___x_3594_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
lean_ctor_set_uint8(v___x_3594_, sizeof(void*)*1, v___x_3592_);
v___x_3595_ = lean_box(0);
v___x_3596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3596_, 0, v_g_3577_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3594_, v_lemmas_3575_, v_ctx_3591_, v___x_3596_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
return v___x_3597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3600_, lean_object* v_lemmas_3601_, lean_object* v_only_3602_, lean_object* v_g_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_){
_start:
{
uint8_t v_only_boxed_3609_; lean_object* v_res_3610_; 
v_only_boxed_3609_ = lean_unbox(v_only_3602_);
v_res_3610_ = l_Lean_MVarId_applyRules(v_cfg_3600_, v_lemmas_3601_, v_only_boxed_3609_, v_g_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
lean_dec(v_a_3605_);
lean_dec_ref(v_a_3604_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3611_, size_t v_sz_3612_, size_t v_i_3613_, lean_object* v_b_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3611_, v_sz_3612_, v_i_3613_, v_b_3614_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3623_, lean_object* v_sz_3624_, lean_object* v_i_3625_, lean_object* v_b_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
size_t v_sz_boxed_3634_; size_t v_i_boxed_3635_; lean_object* v_res_3636_; 
v_sz_boxed_3634_ = lean_unbox_usize(v_sz_3624_);
lean_dec(v_sz_3624_);
v_i_boxed_3635_ = lean_unbox_usize(v_i_3625_);
lean_dec(v_i_3625_);
v_res_3636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3623_, v_sz_boxed_3634_, v_i_boxed_3635_, v_b_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec_ref(v_as_3623_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3637_, size_t v_sz_3638_, size_t v_i_3639_, lean_object* v_b_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3637_, v_sz_3638_, v_i_3639_, v_b_3640_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3649_, lean_object* v_sz_3650_, lean_object* v_i_3651_, lean_object* v_b_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
size_t v_sz_boxed_3660_; size_t v_i_boxed_3661_; lean_object* v_res_3662_; 
v_sz_boxed_3660_ = lean_unbox_usize(v_sz_3650_);
lean_dec(v_sz_3650_);
v_i_boxed_3661_ = lean_unbox_usize(v_i_3651_);
lean_dec(v_i_3651_);
v_res_3662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3649_, v_sz_boxed_3660_, v_i_boxed_3661_, v_b_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec_ref(v_as_3649_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v___x_3671_; uint8_t v___x_3672_; lean_object* v___x_3673_; 
v___x_3671_ = lean_box(0);
v___x_3672_ = 1;
v___x_3673_ = l_Lean_Elab_Term_elabTerm(v_t_3663_, v___x_3671_, v___x_3672_, v___x_3672_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3679_);
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
lean_dec(v_a_3676_);
lean_dec_ref(v_a_3675_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_ref_3688_; uint8_t v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v_ref_3688_ = lean_ctor_get(v___y_3685_, 5);
v___x_3689_ = 0;
v___x_3690_ = l_Lean_SourceInfo_fromRef(v_ref_3688_, v___x_3689_);
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
return v_res_3697_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3698_, lean_object* v_x_3699_){
_start:
{
if (lean_obj_tag(v_x_3699_) == 0)
{
uint8_t v___x_3700_; 
v___x_3700_ = 0;
return v___x_3700_;
}
else
{
lean_object* v_head_3701_; lean_object* v_tail_3702_; uint8_t v___x_3703_; 
v_head_3701_ = lean_ctor_get(v_x_3699_, 0);
v_tail_3702_ = lean_ctor_get(v_x_3699_, 1);
v___x_3703_ = lean_expr_eqv(v_a_3698_, v_head_3701_);
if (v___x_3703_ == 0)
{
v_x_3699_ = v_tail_3702_;
goto _start;
}
else
{
return v___x_3703_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3705_, lean_object* v_x_3706_){
_start:
{
uint8_t v_res_3707_; lean_object* v_r_3708_; 
v_res_3707_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3705_, v_x_3706_);
lean_dec(v_x_3706_);
lean_dec_ref(v_a_3705_);
v_r_3708_ = lean_box(v_res_3707_);
return v_r_3708_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3709_, lean_object* v_x_3710_){
_start:
{
uint8_t v___x_3711_; 
v___x_3711_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3710_, v_ys_3709_);
if (v___x_3711_ == 0)
{
uint8_t v___x_3712_; 
v___x_3712_ = 1;
return v___x_3712_;
}
else
{
uint8_t v___x_3713_; 
v___x_3713_ = 0;
return v___x_3713_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3714_, lean_object* v_x_3715_){
_start:
{
uint8_t v_res_3716_; lean_object* v_r_3717_; 
v_res_3716_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3714_, v_x_3715_);
lean_dec_ref(v_x_3715_);
lean_dec(v_ys_3714_);
v_r_3717_ = lean_box(v_res_3716_);
return v_r_3717_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3718_, lean_object* v_ys_3719_){
_start:
{
lean_object* v___f_3720_; lean_object* v___x_3721_; 
v___f_3720_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3720_, 0, v_ys_3719_);
v___x_3721_ = l_List_filter___redArg(v___f_3720_, v_xs_3718_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3722_, lean_object* v_x_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
if (lean_obj_tag(v_x_3722_) == 0)
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = l_List_reverse___redArg(v_x_3723_);
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
return v___x_3732_;
}
else
{
lean_object* v_head_3733_; lean_object* v_tail_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3752_; 
v_head_3733_ = lean_ctor_get(v_x_3722_, 0);
v_tail_3734_ = lean_ctor_get(v_x_3722_, 1);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_x_3722_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3736_ = v_x_3722_;
v_isShared_3737_ = v_isSharedCheck_3752_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_tail_3734_);
lean_inc(v_head_3733_);
lean_dec(v_x_3722_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3752_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3738_; 
v___x_3738_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3733_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3741_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3739_);
lean_dec_ref(v___x_3738_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 1, v_x_3723_);
lean_ctor_set(v___x_3736_, 0, v_a_3739_);
v___x_3741_ = v___x_3736_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3739_);
lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_x_3723_);
v___x_3741_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
v_x_3722_ = v_tail_3734_;
v_x_3723_ = v___x_3741_;
goto _start;
}
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
lean_del_object(v___x_3736_);
lean_dec(v_tail_3734_);
lean_dec(v_x_3723_);
v_a_3744_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3738_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3738_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3753_, lean_object* v_x_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3753_, v_x_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3763_, uint8_t v_noDefaults_3764_, uint8_t v_star_3765_, lean_object* v_cfg_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
if (v_noDefaults_3764_ == 0)
{
goto v___jp_3774_;
}
else
{
if (v_star_3765_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
lean_dec(v_remove_3763_);
v___x_3793_ = lean_box(0);
v___x_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
return v___x_3794_;
}
else
{
goto v___jp_3774_;
}
}
v___jp_3774_:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref(v___x_3775_);
v___x_3777_ = lean_box(0);
v___x_3778_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3763_, v___x_3777_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_toApplyRulesConfig_3779_; lean_object* v_a_3780_; uint8_t v_symm_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v_toApplyRulesConfig_3779_ = lean_ctor_get(v_cfg_3766_, 0);
v_a_3780_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3780_);
lean_dec_ref(v___x_3778_);
v_symm_3781_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3779_, sizeof(void*)*2 + 1);
v___x_3782_ = lean_array_to_list(v_a_3776_);
v___x_3783_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3782_, v_a_3780_);
v___x_3784_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3781_, v___x_3783_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
return v___x_3784_;
}
else
{
lean_dec(v_a_3776_);
return v___x_3778_;
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_dec(v_remove_3763_);
v_a_3785_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3775_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3775_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3795_, lean_object* v_noDefaults_3796_, lean_object* v_star_3797_, lean_object* v_cfg_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
uint8_t v_noDefaults_boxed_3806_; uint8_t v_star_boxed_3807_; lean_object* v_res_3808_; 
v_noDefaults_boxed_3806_ = lean_unbox(v_noDefaults_3796_);
v_star_boxed_3807_ = lean_unbox(v_star_3797_);
v_res_3808_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3795_, v_noDefaults_boxed_3806_, v_star_boxed_3807_, v_cfg_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec_ref(v_cfg_3798_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3809_, size_t v_i_3810_, size_t v_stop_3811_, lean_object* v_b_3812_){
_start:
{
uint8_t v___x_3813_; 
v___x_3813_ = lean_usize_dec_eq(v_i_3810_, v_stop_3811_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; lean_object* v___x_3815_; size_t v___x_3816_; size_t v___x_3817_; 
v___x_3814_ = lean_array_uget_borrowed(v_as_3809_, v_i_3810_);
v___x_3815_ = l_Array_append___redArg(v_b_3812_, v___x_3814_);
v___x_3816_ = ((size_t)1ULL);
v___x_3817_ = lean_usize_add(v_i_3810_, v___x_3816_);
v_i_3810_ = v___x_3817_;
v_b_3812_ = v___x_3815_;
goto _start;
}
else
{
return v_b_3812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3819_, lean_object* v_i_3820_, lean_object* v_stop_3821_, lean_object* v_b_3822_){
_start:
{
size_t v_i_boxed_3823_; size_t v_stop_boxed_3824_; lean_object* v_res_3825_; 
v_i_boxed_3823_ = lean_unbox_usize(v_i_3820_);
lean_dec(v_i_3820_);
v_stop_boxed_3824_ = lean_unbox_usize(v_stop_3821_);
lean_dec(v_stop_3821_);
v_res_3825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3819_, v_i_boxed_3823_, v_stop_boxed_3824_, v_b_3822_);
lean_dec_ref(v_as_3819_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3826_, lean_object* v_a_3827_){
_start:
{
if (lean_obj_tag(v_a_3826_) == 0)
{
lean_object* v___x_3828_; 
v___x_3828_ = l_List_reverse___redArg(v_a_3827_);
return v___x_3828_;
}
else
{
lean_object* v_head_3829_; lean_object* v_tail_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3839_; 
v_head_3829_ = lean_ctor_get(v_a_3826_, 0);
v_tail_3830_ = lean_ctor_get(v_a_3826_, 1);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_a_3826_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3832_ = v_a_3826_;
v_isShared_3833_ = v_isSharedCheck_3839_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_tail_3830_);
lean_inc(v_head_3829_);
lean_dec(v_a_3826_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3839_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3834_; lean_object* v___x_3836_; 
v___x_3834_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3834_, 0, v_head_3829_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 1, v_a_3827_);
lean_ctor_set(v___x_3832_, 0, v___x_3834_);
v___x_3836_ = v___x_3832_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3834_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_a_3827_);
v___x_3836_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
v_a_3826_ = v_tail_3830_;
v_a_3827_ = v___x_3836_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3840_, size_t v_i_3841_, lean_object* v_bs_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
uint8_t v___x_3846_; 
v___x_3846_ = lean_usize_dec_lt(v_i_3841_, v_sz_3840_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; 
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v_bs_3842_);
return v___x_3847_;
}
else
{
lean_object* v_v_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v_v_3848_ = lean_array_uget_borrowed(v_bs_3842_, v_i_3841_);
v___x_3849_ = l_Lean_Syntax_getId(v_v_3848_);
v___x_3850_ = l_Lean_labelled(v___x_3849_, v___y_3843_, v___y_3844_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; lean_object* v___x_3852_; lean_object* v_bs_x27_3853_; size_t v___x_3854_; size_t v___x_3855_; lean_object* v___x_3856_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref(v___x_3850_);
v___x_3852_ = lean_unsigned_to_nat(0u);
v_bs_x27_3853_ = lean_array_uset(v_bs_3842_, v_i_3841_, v___x_3852_);
v___x_3854_ = ((size_t)1ULL);
v___x_3855_ = lean_usize_add(v_i_3841_, v___x_3854_);
v___x_3856_ = lean_array_uset(v_bs_x27_3853_, v_i_3841_, v_a_3851_);
v_i_3841_ = v___x_3855_;
v_bs_3842_ = v___x_3856_;
goto _start;
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_dec_ref(v_bs_3842_);
v_a_3858_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3850_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3850_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3866_, lean_object* v_i_3867_, lean_object* v_bs_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
size_t v_sz_boxed_3872_; size_t v_i_boxed_3873_; lean_object* v_res_3874_; 
v_sz_boxed_3872_ = lean_unbox_usize(v_sz_3866_);
lean_dec(v_sz_3866_);
v_i_boxed_3873_ = lean_unbox_usize(v_i_3867_);
lean_dec(v_i_3867_);
v_res_3874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3872_, v_i_boxed_3873_, v_bs_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3875_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
if (lean_obj_tag(v_a_3893_) == 0)
{
lean_object* v___x_3895_; 
v___x_3895_ = l_List_reverse___redArg(v_a_3894_);
return v___x_3895_;
}
else
{
lean_object* v_head_3896_; lean_object* v_tail_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3906_; 
v_head_3896_ = lean_ctor_get(v_a_3893_, 0);
v_tail_3897_ = lean_ctor_get(v_a_3893_, 1);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_a_3893_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3899_ = v_a_3893_;
v_isShared_3900_ = v_isSharedCheck_3906_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_tail_3897_);
lean_inc(v_head_3896_);
lean_dec(v_a_3893_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3906_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___f_3901_; lean_object* v___x_3903_; 
v___f_3901_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3901_, 0, v_head_3896_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 1, v_a_3894_);
lean_ctor_set(v___x_3899_, 0, v___f_3901_);
v___x_3903_ = v___x_3899_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___f_3901_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_a_3894_);
v___x_3903_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
v_a_3893_ = v_tail_3897_;
v_a_3894_ = v___x_3903_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3908_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3909_ = l_Lean_stringToMessageData(v___x_3908_);
return v___x_3909_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3912_ = l_String_toRawSubstring_x27(v___x_3911_);
return v___x_3912_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3916_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3917_ = l_String_toRawSubstring_x27(v___x_3916_);
return v___x_3917_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3922_ = l_String_toRawSubstring_x27(v___x_3921_);
return v___x_3922_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3926_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3927_ = l_String_toRawSubstring_x27(v___x_3926_);
return v___x_3927_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3957_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3958_ = l_Lean_stringToMessageData(v___x_3957_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3959_, uint8_t v_star_3960_, lean_object* v_add_3961_, lean_object* v_remove_3962_, lean_object* v_use_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_){
_start:
{
lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___f_3994_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; 
v___x_3992_ = lean_box(v_noDefaults_3959_);
v___x_3993_ = lean_box(v_star_3960_);
lean_inc(v_remove_3962_);
v___f_3994_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3994_, 0, v_remove_3962_);
lean_closure_set(v___f_3994_, 1, v___x_3992_);
lean_closure_set(v___f_3994_, 2, v___x_3993_);
if (v_star_3960_ == 0)
{
v___y_4011_ = v_a_3964_;
v___y_4012_ = v_a_3965_;
v___y_4013_ = v_a_3966_;
v___y_4014_ = v_a_3967_;
goto v___jp_4010_;
}
else
{
if (v_noDefaults_3959_ == 0)
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
lean_dec_ref(v___f_3994_);
lean_dec_ref(v_use_3963_);
lean_dec(v_remove_3962_);
lean_dec(v_add_3961_);
v___x_4073_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_4074_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_4073_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_4074_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4074_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
else
{
v___y_4011_ = v_a_3964_;
v___y_4012_ = v_a_3965_;
v___y_4013_ = v_a_3966_;
v___y_4014_ = v_a_3967_;
goto v___jp_4010_;
}
}
v___jp_3969_:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___y_3970_);
lean_ctor_set(v___x_3972_, 1, v___y_3971_);
v___x_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
return v___x_3973_;
}
v___jp_3974_:
{
uint8_t v___x_3981_; 
v___x_3981_ = l_List_isEmpty___redArg(v_remove_3962_);
lean_dec(v_remove_3962_);
if (v___x_3981_ == 0)
{
if (v_noDefaults_3959_ == 0)
{
v___y_3970_ = v___y_3980_;
v___y_3971_ = v___y_3976_;
goto v___jp_3969_;
}
else
{
if (v_star_3960_ == 0)
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3976_);
v___x_3982_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3983_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3982_, v___y_3979_, v___y_3975_, v___y_3978_, v___y_3977_);
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3983_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
else
{
v___y_3970_ = v___y_3980_;
v___y_3971_ = v___y_3976_;
goto v___jp_3969_;
}
}
}
else
{
v___y_3970_ = v___y_3980_;
v___y_3971_ = v___y_3976_;
goto v___jp_3969_;
}
}
v___jp_3995_:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4003_ = lean_array_to_list(v___y_4002_);
lean_inc(v___y_3997_);
v___x_4004_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_4003_, v___y_3997_);
if (v_noDefaults_3959_ == 0)
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4005_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3961_, v___y_3997_);
v___x_4006_ = l_List_appendTR___redArg(v___x_4005_, v___x_4004_);
v___x_4007_ = l_List_appendTR___redArg(v___x_4006_, v___y_4001_);
v___y_3975_ = v___y_3996_;
v___y_3976_ = v___f_3994_;
v___y_3977_ = v___y_3999_;
v___y_3978_ = v___y_3998_;
v___y_3979_ = v___y_4000_;
v___y_3980_ = v___x_4007_;
goto v___jp_3974_;
}
else
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
lean_dec(v___y_4001_);
v___x_4008_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3961_, v___y_3997_);
v___x_4009_ = l_List_appendTR___redArg(v___x_4008_, v___x_4004_);
v___y_3975_ = v___y_3996_;
v___y_3976_ = v___f_3994_;
v___y_3977_ = v___y_3999_;
v___y_3978_ = v___y_3998_;
v___y_3979_ = v___y_4000_;
v___y_3980_ = v___x_4009_;
goto v___jp_3974_;
}
}
v___jp_4010_:
{
lean_object* v_ref_4015_; lean_object* v_quotContext_4016_; lean_object* v_currMacroScope_4017_; lean_object* v___x_4018_; lean_object* v_a_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v_a_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v_a_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; size_t v_sz_4031_; size_t v___x_4032_; lean_object* v___x_4033_; 
v_ref_4015_ = lean_ctor_get(v___y_4013_, 5);
v_quotContext_4016_ = lean_ctor_get(v___y_4013_, 10);
v_currMacroScope_4017_ = lean_ctor_get(v___y_4013_, 11);
v___x_4018_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_a_4019_);
lean_dec_ref(v___x_4018_);
v___x_4020_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_4021_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref(v___x_4021_);
v___x_4023_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_4017_, 2);
lean_inc_n(v_quotContext_4016_, 2);
v___x_4024_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4023_, v_currMacroScope_4017_);
v___x_4025_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_4026_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref(v___x_4026_);
v___x_4028_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_4029_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4028_, v_currMacroScope_4017_);
v___x_4030_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_4031_ = lean_array_size(v_use_3963_);
v___x_4032_ = ((size_t)0ULL);
v___x_4033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4031_, v___x_4032_, v_use_3963_, v___y_4013_, v___y_4014_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; uint8_t v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; uint8_t v___x_4059_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref(v___x_4033_);
v___x_4035_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc_n(v_currMacroScope_4017_, 2);
lean_inc_n(v_quotContext_4016_, 2);
v___x_4036_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4035_, v_currMacroScope_4017_);
v___x_4037_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_4038_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
v___x_4039_ = l_Lean_addMacroScope(v_quotContext_4016_, v___x_4038_, v_currMacroScope_4017_);
v___x_4040_ = 0;
v___x_4041_ = l_Lean_SourceInfo_fromRef(v_ref_4015_, v___x_4040_);
v___x_4042_ = lean_box(0);
v___x_4043_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_4044_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4041_);
lean_ctor_set(v___x_4044_, 1, v___x_4020_);
lean_ctor_set(v___x_4044_, 2, v___x_4024_);
lean_ctor_set(v___x_4044_, 3, v___x_4043_);
v___x_4045_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_4046_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4046_, 0, v_a_4019_);
lean_ctor_set(v___x_4046_, 1, v___x_4025_);
lean_ctor_set(v___x_4046_, 2, v___x_4029_);
lean_ctor_set(v___x_4046_, 3, v___x_4045_);
v___x_4047_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_4048_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4048_, 0, v_a_4022_);
lean_ctor_set(v___x_4048_, 1, v___x_4030_);
lean_ctor_set(v___x_4048_, 2, v___x_4036_);
lean_ctor_set(v___x_4048_, 3, v___x_4047_);
v___x_4049_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_4050_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4050_, 0, v_a_4027_);
lean_ctor_set(v___x_4050_, 1, v___x_4037_);
lean_ctor_set(v___x_4050_, 2, v___x_4039_);
lean_ctor_set(v___x_4050_, 3, v___x_4049_);
v___x_4051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
lean_ctor_set(v___x_4051_, 1, v___x_4042_);
v___x_4052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4048_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
v___x_4053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4046_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
v___x_4054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4044_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
v___x_4055_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_4054_, v___x_4042_);
v___x_4056_ = lean_unsigned_to_nat(0u);
v___x_4057_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_4058_ = lean_array_get_size(v_a_4034_);
v___x_4059_ = lean_nat_dec_lt(v___x_4056_, v___x_4058_);
if (v___x_4059_ == 0)
{
lean_dec(v_a_4034_);
v___y_3996_ = v___y_4012_;
v___y_3997_ = v___x_4042_;
v___y_3998_ = v___y_4013_;
v___y_3999_ = v___y_4014_;
v___y_4000_ = v___y_4011_;
v___y_4001_ = v___x_4055_;
v___y_4002_ = v___x_4057_;
goto v___jp_3995_;
}
else
{
uint8_t v___x_4060_; 
v___x_4060_ = lean_nat_dec_le(v___x_4058_, v___x_4058_);
if (v___x_4060_ == 0)
{
if (v___x_4059_ == 0)
{
lean_dec(v_a_4034_);
v___y_3996_ = v___y_4012_;
v___y_3997_ = v___x_4042_;
v___y_3998_ = v___y_4013_;
v___y_3999_ = v___y_4014_;
v___y_4000_ = v___y_4011_;
v___y_4001_ = v___x_4055_;
v___y_4002_ = v___x_4057_;
goto v___jp_3995_;
}
else
{
size_t v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = lean_usize_of_nat(v___x_4058_);
v___x_4062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4034_, v___x_4032_, v___x_4061_, v___x_4057_);
lean_dec(v_a_4034_);
v___y_3996_ = v___y_4012_;
v___y_3997_ = v___x_4042_;
v___y_3998_ = v___y_4013_;
v___y_3999_ = v___y_4014_;
v___y_4000_ = v___y_4011_;
v___y_4001_ = v___x_4055_;
v___y_4002_ = v___x_4062_;
goto v___jp_3995_;
}
}
else
{
size_t v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_usize_of_nat(v___x_4058_);
v___x_4064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4034_, v___x_4032_, v___x_4063_, v___x_4057_);
lean_dec(v_a_4034_);
v___y_3996_ = v___y_4012_;
v___y_3997_ = v___x_4042_;
v___y_3998_ = v___y_4013_;
v___y_3999_ = v___y_4014_;
v___y_4000_ = v___y_4011_;
v___y_4001_ = v___x_4055_;
v___y_4002_ = v___x_4064_;
goto v___jp_3995_;
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec(v___x_4029_);
lean_dec(v_a_4027_);
lean_dec(v___x_4024_);
lean_dec(v_a_4022_);
lean_dec(v_a_4019_);
lean_dec_ref(v___f_3994_);
lean_dec(v_remove_3962_);
lean_dec(v_add_3961_);
v_a_4065_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4033_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4033_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_4083_, lean_object* v_star_4084_, lean_object* v_add_4085_, lean_object* v_remove_4086_, lean_object* v_use_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_){
_start:
{
uint8_t v_noDefaults_boxed_4093_; uint8_t v_star_boxed_4094_; lean_object* v_res_4095_; 
v_noDefaults_boxed_4093_ = lean_unbox(v_noDefaults_4083_);
v_star_boxed_4094_ = lean_unbox(v_star_4084_);
v_res_4095_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_4093_, v_star_boxed_4094_, v_add_4085_, v_remove_4086_, v_use_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t v_sz_4096_, size_t v_i_4097_, lean_object* v_bs_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4096_, v_i_4097_, v_bs_4098_, v___y_4101_, v___y_4102_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_sz_4105_, lean_object* v_i_4106_, lean_object* v_bs_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
size_t v_sz_boxed_4113_; size_t v_i_boxed_4114_; lean_object* v_res_4115_; 
v_sz_boxed_4113_ = lean_unbox_usize(v_sz_4105_);
lean_dec(v_sz_4105_);
v_i_boxed_4114_ = lean_unbox_usize(v_i_4106_);
lean_dec(v_i_4106_);
v_res_4115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_4113_, v_i_boxed_4114_, v_bs_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
return v_res_4115_;
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
