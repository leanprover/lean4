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
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0;
static const lean_string_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t v___x_252_, lean_object* v_x_253_, lean_object* v_x_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_object* v___x_260_; 
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v_x_254_);
return v___x_260_;
}
else
{
lean_object* v_head_261_; lean_object* v_tail_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_285_; 
v_head_261_ = lean_ctor_get(v_x_253_, 0);
v_tail_262_ = lean_ctor_get(v_x_253_, 1);
v_isSharedCheck_285_ = !lean_is_exclusive(v_x_253_);
if (v_isSharedCheck_285_ == 0)
{
v___x_264_ = v_x_253_;
v_isShared_265_ = v_isSharedCheck_285_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_tail_262_);
lean_inc(v_head_261_);
lean_dec(v_x_253_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_285_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_271_; 
lean_inc(v_head_261_);
v___x_271_ = l_Lean_MVarId_inferInstance(v_head_261_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_dec_ref_known(v___x_271_, 1);
if (v___x_252_ == 0)
{
lean_del_object(v___x_264_);
lean_dec(v_head_261_);
v_x_253_ = v_tail_262_;
goto _start;
}
else
{
goto v___jp_266_;
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_284_; 
v_a_273_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_284_ == 0)
{
v___x_275_ = v___x_271_;
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_271_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
uint8_t v___y_278_; uint8_t v___x_282_; 
v___x_282_ = l_Lean_Exception_isInterrupt(v_a_273_);
if (v___x_282_ == 0)
{
uint8_t v___x_283_; 
lean_inc(v_a_273_);
v___x_283_ = l_Lean_Exception_isRuntime(v_a_273_);
v___y_278_ = v___x_283_;
goto v___jp_277_;
}
else
{
v___y_278_ = v___x_282_;
goto v___jp_277_;
}
v___jp_277_:
{
if (v___y_278_ == 0)
{
lean_del_object(v___x_275_);
lean_dec(v_a_273_);
goto v___jp_266_;
}
else
{
lean_object* v___x_280_; 
lean_del_object(v___x_264_);
lean_dec(v_tail_262_);
lean_dec(v_head_261_);
lean_dec(v_x_254_);
if (v_isShared_276_ == 0)
{
v___x_280_ = v___x_275_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_273_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
v___jp_266_:
{
lean_object* v___x_268_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 1, v_x_254_);
v___x_268_ = v___x_264_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_head_261_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_x_254_);
v___x_268_ = v_reuseFailAlloc_270_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
v_x_253_ = v_tail_262_;
v_x_254_ = v___x_268_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object* v___x_286_, lean_object* v_x_287_, lean_object* v_x_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
uint8_t v___x_13996__boxed_294_; lean_object* v_res_295_; 
v___x_13996__boxed_294_ = lean_unbox(v___x_286_);
v_res_295_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_13996__boxed_294_, v_x_287_, v_x_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(lean_object* v_msgData_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; lean_object* v_env_303_; lean_object* v___x_304_; lean_object* v_mctx_305_; lean_object* v_lctx_306_; lean_object* v_options_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_302_ = lean_st_ref_get(v___y_300_);
v_env_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc_ref(v_env_303_);
lean_dec(v___x_302_);
v___x_304_ = lean_st_ref_get(v___y_298_);
v_mctx_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc_ref(v_mctx_305_);
lean_dec(v___x_304_);
v_lctx_306_ = lean_ctor_get(v___y_297_, 2);
v_options_307_ = lean_ctor_get(v___y_299_, 2);
lean_inc_ref(v_options_307_);
lean_inc_ref(v_lctx_306_);
v___x_308_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_308_, 0, v_env_303_);
lean_ctor_set(v___x_308_, 1, v_mctx_305_);
lean_ctor_set(v___x_308_, 2, v_lctx_306_);
lean_ctor_set(v___x_308_, 3, v_options_307_);
v___x_309_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_msgData_296_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msgData_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t v_sz_318_, size_t v_i_319_, lean_object* v_bs_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = lean_usize_dec_lt(v_i_319_, v_sz_318_);
if (v___x_321_ == 0)
{
return v_bs_320_;
}
else
{
lean_object* v_v_322_; lean_object* v_msg_323_; lean_object* v___x_324_; lean_object* v_bs_x27_325_; size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v_v_322_ = lean_array_uget_borrowed(v_bs_320_, v_i_319_);
v_msg_323_ = lean_ctor_get(v_v_322_, 1);
lean_inc_ref(v_msg_323_);
v___x_324_ = lean_unsigned_to_nat(0u);
v_bs_x27_325_ = lean_array_uset(v_bs_320_, v_i_319_, v___x_324_);
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_add(v_i_319_, v___x_326_);
v___x_328_ = lean_array_uset(v_bs_x27_325_, v_i_319_, v_msg_323_);
v_i_319_ = v___x_327_;
v_bs_320_ = v___x_328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_330_, lean_object* v_i_331_, lean_object* v_bs_332_){
_start:
{
size_t v_sz_boxed_333_; size_t v_i_boxed_334_; lean_object* v_res_335_; 
v_sz_boxed_333_ = lean_unbox_usize(v_sz_330_);
lean_dec(v_sz_330_);
v_i_boxed_334_ = lean_unbox_usize(v_i_331_);
lean_dec(v_i_331_);
v_res_335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_boxed_333_, v_i_boxed_334_, v_bs_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object* v_oldTraces_336_, lean_object* v_data_337_, lean_object* v_ref_338_, lean_object* v_msg_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_fileName_345_; lean_object* v_fileMap_346_; lean_object* v_options_347_; lean_object* v_currRecDepth_348_; lean_object* v_maxRecDepth_349_; lean_object* v_ref_350_; lean_object* v_currNamespace_351_; lean_object* v_openDecls_352_; lean_object* v_initHeartbeats_353_; lean_object* v_maxHeartbeats_354_; lean_object* v_quotContext_355_; lean_object* v_currMacroScope_356_; uint8_t v_diag_357_; lean_object* v_cancelTk_x3f_358_; uint8_t v_suppressElabErrors_359_; lean_object* v_inheritedTraceOptions_360_; lean_object* v___x_361_; lean_object* v_traceState_362_; lean_object* v_traces_363_; lean_object* v_ref_364_; lean_object* v___x_365_; lean_object* v___x_366_; size_t v_sz_367_; size_t v___x_368_; lean_object* v___x_369_; lean_object* v_msg_370_; lean_object* v___x_371_; lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_409_; 
v_fileName_345_ = lean_ctor_get(v___y_342_, 0);
v_fileMap_346_ = lean_ctor_get(v___y_342_, 1);
v_options_347_ = lean_ctor_get(v___y_342_, 2);
v_currRecDepth_348_ = lean_ctor_get(v___y_342_, 3);
v_maxRecDepth_349_ = lean_ctor_get(v___y_342_, 4);
v_ref_350_ = lean_ctor_get(v___y_342_, 5);
v_currNamespace_351_ = lean_ctor_get(v___y_342_, 6);
v_openDecls_352_ = lean_ctor_get(v___y_342_, 7);
v_initHeartbeats_353_ = lean_ctor_get(v___y_342_, 8);
v_maxHeartbeats_354_ = lean_ctor_get(v___y_342_, 9);
v_quotContext_355_ = lean_ctor_get(v___y_342_, 10);
v_currMacroScope_356_ = lean_ctor_get(v___y_342_, 11);
v_diag_357_ = lean_ctor_get_uint8(v___y_342_, sizeof(void*)*14);
v_cancelTk_x3f_358_ = lean_ctor_get(v___y_342_, 12);
v_suppressElabErrors_359_ = lean_ctor_get_uint8(v___y_342_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_360_ = lean_ctor_get(v___y_342_, 13);
v___x_361_ = lean_st_ref_get(v___y_343_);
v_traceState_362_ = lean_ctor_get(v___x_361_, 4);
lean_inc_ref(v_traceState_362_);
lean_dec(v___x_361_);
v_traces_363_ = lean_ctor_get(v_traceState_362_, 0);
lean_inc_ref(v_traces_363_);
lean_dec_ref(v_traceState_362_);
v_ref_364_ = l_Lean_replaceRef(v_ref_338_, v_ref_350_);
lean_inc_ref(v_inheritedTraceOptions_360_);
lean_inc(v_cancelTk_x3f_358_);
lean_inc(v_currMacroScope_356_);
lean_inc(v_quotContext_355_);
lean_inc(v_maxHeartbeats_354_);
lean_inc(v_initHeartbeats_353_);
lean_inc(v_openDecls_352_);
lean_inc(v_currNamespace_351_);
lean_inc(v_maxRecDepth_349_);
lean_inc(v_currRecDepth_348_);
lean_inc_ref(v_options_347_);
lean_inc_ref(v_fileMap_346_);
lean_inc_ref(v_fileName_345_);
v___x_365_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_365_, 0, v_fileName_345_);
lean_ctor_set(v___x_365_, 1, v_fileMap_346_);
lean_ctor_set(v___x_365_, 2, v_options_347_);
lean_ctor_set(v___x_365_, 3, v_currRecDepth_348_);
lean_ctor_set(v___x_365_, 4, v_maxRecDepth_349_);
lean_ctor_set(v___x_365_, 5, v_ref_364_);
lean_ctor_set(v___x_365_, 6, v_currNamespace_351_);
lean_ctor_set(v___x_365_, 7, v_openDecls_352_);
lean_ctor_set(v___x_365_, 8, v_initHeartbeats_353_);
lean_ctor_set(v___x_365_, 9, v_maxHeartbeats_354_);
lean_ctor_set(v___x_365_, 10, v_quotContext_355_);
lean_ctor_set(v___x_365_, 11, v_currMacroScope_356_);
lean_ctor_set(v___x_365_, 12, v_cancelTk_x3f_358_);
lean_ctor_set(v___x_365_, 13, v_inheritedTraceOptions_360_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*14, v_diag_357_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*14 + 1, v_suppressElabErrors_359_);
v___x_366_ = l_Lean_PersistentArray_toArray___redArg(v_traces_363_);
lean_dec_ref(v_traces_363_);
v_sz_367_ = lean_array_size(v___x_366_);
v___x_368_ = ((size_t)0ULL);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_367_, v___x_368_, v___x_366_);
v_msg_370_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_370_, 0, v_data_337_);
lean_ctor_set(v_msg_370_, 1, v_msg_339_);
lean_ctor_set(v_msg_370_, 2, v___x_369_);
v___x_371_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_370_, v___y_340_, v___y_341_, v___x_365_, v___y_343_);
lean_dec_ref_known(v___x_365_, 14);
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_409_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_409_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_409_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v_traceState_377_; lean_object* v_env_378_; lean_object* v_nextMacroScope_379_; lean_object* v_ngen_380_; lean_object* v_auxDeclNGen_381_; lean_object* v_cache_382_; lean_object* v_messages_383_; lean_object* v_infoState_384_; lean_object* v_snapshotTasks_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_408_; 
v___x_376_ = lean_st_ref_take(v___y_343_);
v_traceState_377_ = lean_ctor_get(v___x_376_, 4);
v_env_378_ = lean_ctor_get(v___x_376_, 0);
v_nextMacroScope_379_ = lean_ctor_get(v___x_376_, 1);
v_ngen_380_ = lean_ctor_get(v___x_376_, 2);
v_auxDeclNGen_381_ = lean_ctor_get(v___x_376_, 3);
v_cache_382_ = lean_ctor_get(v___x_376_, 5);
v_messages_383_ = lean_ctor_get(v___x_376_, 6);
v_infoState_384_ = lean_ctor_get(v___x_376_, 7);
v_snapshotTasks_385_ = lean_ctor_get(v___x_376_, 8);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_408_ == 0)
{
v___x_387_ = v___x_376_;
v_isShared_388_ = v_isSharedCheck_408_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_snapshotTasks_385_);
lean_inc(v_infoState_384_);
lean_inc(v_messages_383_);
lean_inc(v_cache_382_);
lean_inc(v_traceState_377_);
lean_inc(v_auxDeclNGen_381_);
lean_inc(v_ngen_380_);
lean_inc(v_nextMacroScope_379_);
lean_inc(v_env_378_);
lean_dec(v___x_376_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_408_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
uint64_t v_tid_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_406_; 
v_tid_389_ = lean_ctor_get_uint64(v_traceState_377_, sizeof(void*)*1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_traceState_377_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v_traceState_377_, 0);
lean_dec(v_unused_407_);
v___x_391_ = v_traceState_377_;
v_isShared_392_ = v_isSharedCheck_406_;
goto v_resetjp_390_;
}
else
{
lean_dec(v_traceState_377_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_406_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v_ref_338_);
lean_ctor_set(v___x_393_, 1, v_a_372_);
v___x_394_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_336_, v___x_393_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_394_);
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_394_);
lean_ctor_set_uint64(v_reuseFailAlloc_405_, sizeof(void*)*1, v_tid_389_);
v___x_396_ = v_reuseFailAlloc_405_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_398_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 4, v___x_396_);
v___x_398_ = v___x_387_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_env_378_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_nextMacroScope_379_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_ngen_380_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_auxDeclNGen_381_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_404_, 5, v_cache_382_);
lean_ctor_set(v_reuseFailAlloc_404_, 6, v_messages_383_);
lean_ctor_set(v_reuseFailAlloc_404_, 7, v_infoState_384_);
lean_ctor_set(v_reuseFailAlloc_404_, 8, v_snapshotTasks_385_);
v___x_398_ = v_reuseFailAlloc_404_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_399_ = lean_st_ref_set(v___y_343_, v___x_398_);
v___x_400_ = lean_box(0);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_400_);
v___x_402_ = v___x_374_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_oldTraces_410_, lean_object* v_data_411_, lean_object* v_ref_412_, lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_410_, v_data_411_, v_ref_412_, v_msg_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_419_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_e_420_){
_start:
{
if (lean_obj_tag(v_e_420_) == 0)
{
uint8_t v___x_421_; 
v___x_421_ = 2;
return v___x_421_;
}
else
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_e_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_423_);
lean_dec_ref(v_e_423_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_426_, lean_object* v_opt_427_){
_start:
{
lean_object* v_name_428_; lean_object* v_defValue_429_; lean_object* v_map_430_; lean_object* v___x_431_; 
v_name_428_ = lean_ctor_get(v_opt_427_, 0);
v_defValue_429_ = lean_ctor_get(v_opt_427_, 1);
v_map_430_ = lean_ctor_get(v_opts_426_, 0);
v___x_431_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_430_, v_name_428_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_inc(v_defValue_429_);
return v_defValue_429_;
}
else
{
lean_object* v_val_432_; 
v_val_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_val_432_);
lean_dec_ref_known(v___x_431_, 1);
if (lean_obj_tag(v_val_432_) == 3)
{
lean_object* v_v_433_; 
v_v_433_ = lean_ctor_get(v_val_432_, 0);
lean_inc(v_v_433_);
lean_dec_ref_known(v_val_432_, 1);
return v_v_433_;
}
else
{
lean_dec(v_val_432_);
lean_inc(v_defValue_429_);
return v_defValue_429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_434_, lean_object* v_opt_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_434_, v_opt_435_);
lean_dec_ref(v_opt_435_);
lean_dec_ref(v_opts_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object* v_x_437_){
_start:
{
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v_a_439_ = lean_ctor_get(v_x_437_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v_x_437_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v_x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set_tag(v___x_441_, 1);
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_a_447_ = lean_ctor_get(v_x_437_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v_x_437_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v_x_437_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 0);
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object* v_x_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_455_);
return v_res_457_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0(void){
_start:
{
lean_object* v___x_458_; double v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_float_of_nat(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3(void){
_start:
{
lean_object* v___x_463_; double v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(1000u);
v___x_464_ = lean_float_of_nat(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_465_, uint8_t v_collapsed_466_, lean_object* v_tag_467_, lean_object* v_opts_468_, uint8_t v_clsEnabled_469_, lean_object* v_oldTraces_470_, lean_object* v_msg_471_, lean_object* v_resStartStop_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_fst_478_; lean_object* v_snd_479_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v_data_483_; lean_object* v_fst_494_; lean_object* v_snd_495_; lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___y_499_; lean_object* v_a_500_; uint8_t v___y_515_; double v___y_546_; 
v_fst_478_ = lean_ctor_get(v_resStartStop_472_, 0);
lean_inc(v_fst_478_);
v_snd_479_ = lean_ctor_get(v_resStartStop_472_, 1);
lean_inc(v_snd_479_);
lean_dec_ref(v_resStartStop_472_);
v_fst_494_ = lean_ctor_get(v_snd_479_, 0);
lean_inc(v_fst_494_);
v_snd_495_ = lean_ctor_get(v_snd_479_, 1);
lean_inc(v_snd_495_);
lean_dec(v_snd_479_);
v___x_496_ = l_Lean_trace_profiler;
v___x_497_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_468_, v___x_496_);
if (v___x_497_ == 0)
{
v___y_515_ = v___x_497_;
goto v___jp_514_;
}
else
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = l_Lean_trace_profiler_useHeartbeats;
v___x_552_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_468_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; double v___x_555_; double v___x_556_; double v___x_557_; 
v___x_553_ = l_Lean_trace_profiler_threshold;
v___x_554_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_468_, v___x_553_);
v___x_555_ = lean_float_of_nat(v___x_554_);
v___x_556_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3);
v___x_557_ = lean_float_div(v___x_555_, v___x_556_);
v___y_546_ = v___x_557_;
goto v___jp_545_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; double v___x_560_; 
v___x_558_ = l_Lean_trace_profiler_threshold;
v___x_559_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_468_, v___x_558_);
v___x_560_ = lean_float_of_nat(v___x_559_);
v___y_546_ = v___x_560_;
goto v___jp_545_;
}
}
v___jp_480_:
{
lean_object* v___x_484_; 
lean_inc(v___y_481_);
v___x_484_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_470_, v_data_483_, v___y_481_, v___y_482_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v___x_485_; 
lean_dec_ref_known(v___x_484_, 1);
v___x_485_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_478_);
return v___x_485_;
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec(v_fst_478_);
v_a_486_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_484_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_484_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
v___jp_498_:
{
uint8_t v_result_501_; lean_object* v___x_502_; lean_object* v___x_503_; double v___x_504_; lean_object* v_data_505_; 
v_result_501_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_fst_478_);
v___x_502_ = lean_box(v_result_501_);
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
v___x_504_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0);
lean_inc_ref(v_tag_467_);
lean_inc_ref(v___x_503_);
lean_inc(v_cls_465_);
v_data_505_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_505_, 0, v_cls_465_);
lean_ctor_set(v_data_505_, 1, v___x_503_);
lean_ctor_set(v_data_505_, 2, v_tag_467_);
lean_ctor_set_float(v_data_505_, sizeof(void*)*3, v___x_504_);
lean_ctor_set_float(v_data_505_, sizeof(void*)*3 + 8, v___x_504_);
lean_ctor_set_uint8(v_data_505_, sizeof(void*)*3 + 16, v_collapsed_466_);
if (v___x_497_ == 0)
{
lean_dec_ref_known(v___x_503_, 1);
lean_dec(v_snd_495_);
lean_dec(v_fst_494_);
lean_dec_ref(v_tag_467_);
lean_dec(v_cls_465_);
v___y_481_ = v___y_499_;
v___y_482_ = v_a_500_;
v_data_483_ = v_data_505_;
goto v___jp_480_;
}
else
{
lean_object* v_data_506_; double v___x_507_; double v___x_508_; 
lean_dec_ref_known(v_data_505_, 3);
v_data_506_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_506_, 0, v_cls_465_);
lean_ctor_set(v_data_506_, 1, v___x_503_);
lean_ctor_set(v_data_506_, 2, v_tag_467_);
v___x_507_ = lean_unbox_float(v_fst_494_);
lean_dec(v_fst_494_);
lean_ctor_set_float(v_data_506_, sizeof(void*)*3, v___x_507_);
v___x_508_ = lean_unbox_float(v_snd_495_);
lean_dec(v_snd_495_);
lean_ctor_set_float(v_data_506_, sizeof(void*)*3 + 8, v___x_508_);
lean_ctor_set_uint8(v_data_506_, sizeof(void*)*3 + 16, v_collapsed_466_);
v___y_481_ = v___y_499_;
v___y_482_ = v_a_500_;
v_data_483_ = v_data_506_;
goto v___jp_480_;
}
}
v___jp_509_:
{
lean_object* v_ref_510_; lean_object* v___x_511_; 
v_ref_510_ = lean_ctor_get(v___y_475_, 5);
lean_inc(v___y_476_);
lean_inc_ref(v___y_475_);
lean_inc(v___y_474_);
lean_inc_ref(v___y_473_);
lean_inc(v_fst_478_);
v___x_511_ = lean_apply_6(v_msg_471_, v_fst_478_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, lean_box(0));
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___y_499_ = v_ref_510_;
v_a_500_ = v_a_512_;
goto v___jp_498_;
}
else
{
lean_object* v___x_513_; 
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
v___y_499_ = v_ref_510_;
v_a_500_ = v___x_513_;
goto v___jp_498_;
}
}
v___jp_514_:
{
if (v_clsEnabled_469_ == 0)
{
if (v___y_515_ == 0)
{
lean_object* v___x_516_; lean_object* v_traceState_517_; lean_object* v_env_518_; lean_object* v_nextMacroScope_519_; lean_object* v_ngen_520_; lean_object* v_auxDeclNGen_521_; lean_object* v_cache_522_; lean_object* v_messages_523_; lean_object* v_infoState_524_; lean_object* v_snapshotTasks_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_snd_495_);
lean_dec(v_fst_494_);
lean_dec_ref(v_msg_471_);
lean_dec_ref(v_tag_467_);
lean_dec(v_cls_465_);
v___x_516_ = lean_st_ref_take(v___y_476_);
v_traceState_517_ = lean_ctor_get(v___x_516_, 4);
v_env_518_ = lean_ctor_get(v___x_516_, 0);
v_nextMacroScope_519_ = lean_ctor_get(v___x_516_, 1);
v_ngen_520_ = lean_ctor_get(v___x_516_, 2);
v_auxDeclNGen_521_ = lean_ctor_get(v___x_516_, 3);
v_cache_522_ = lean_ctor_get(v___x_516_, 5);
v_messages_523_ = lean_ctor_get(v___x_516_, 6);
v_infoState_524_ = lean_ctor_get(v___x_516_, 7);
v_snapshotTasks_525_ = lean_ctor_get(v___x_516_, 8);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_544_ == 0)
{
v___x_527_ = v___x_516_;
v_isShared_528_ = v_isSharedCheck_544_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_snapshotTasks_525_);
lean_inc(v_infoState_524_);
lean_inc(v_messages_523_);
lean_inc(v_cache_522_);
lean_inc(v_traceState_517_);
lean_inc(v_auxDeclNGen_521_);
lean_inc(v_ngen_520_);
lean_inc(v_nextMacroScope_519_);
lean_inc(v_env_518_);
lean_dec(v___x_516_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_544_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
uint64_t v_tid_529_; lean_object* v_traces_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_543_; 
v_tid_529_ = lean_ctor_get_uint64(v_traceState_517_, sizeof(void*)*1);
v_traces_530_ = lean_ctor_get(v_traceState_517_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v_traceState_517_);
if (v_isSharedCheck_543_ == 0)
{
v___x_532_ = v_traceState_517_;
v_isShared_533_ = v_isSharedCheck_543_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_traces_530_);
lean_dec(v_traceState_517_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_543_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_470_, v_traces_530_);
lean_dec_ref(v_traces_530_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_534_);
lean_ctor_set_uint64(v_reuseFailAlloc_542_, sizeof(void*)*1, v_tid_529_);
v___x_536_ = v_reuseFailAlloc_542_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 4, v___x_536_);
v___x_538_ = v___x_527_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_env_518_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_nextMacroScope_519_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_ngen_520_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_auxDeclNGen_521_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_541_, 5, v_cache_522_);
lean_ctor_set(v_reuseFailAlloc_541_, 6, v_messages_523_);
lean_ctor_set(v_reuseFailAlloc_541_, 7, v_infoState_524_);
lean_ctor_set(v_reuseFailAlloc_541_, 8, v_snapshotTasks_525_);
v___x_538_ = v_reuseFailAlloc_541_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_st_ref_set(v___y_476_, v___x_538_);
v___x_540_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_478_);
return v___x_540_;
}
}
}
}
}
else
{
goto v___jp_509_;
}
}
else
{
goto v___jp_509_;
}
}
v___jp_545_:
{
double v___x_547_; double v___x_548_; double v___x_549_; uint8_t v___x_550_; 
v___x_547_ = lean_unbox_float(v_snd_495_);
v___x_548_ = lean_unbox_float(v_fst_494_);
v___x_549_ = lean_float_sub(v___x_547_, v___x_548_);
v___x_550_ = lean_float_decLt(v___y_546_, v___x_549_);
v___y_515_ = v___x_550_;
goto v___jp_514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_561_, lean_object* v_collapsed_562_, lean_object* v_tag_563_, lean_object* v_opts_564_, lean_object* v_clsEnabled_565_, lean_object* v_oldTraces_566_, lean_object* v_msg_567_, lean_object* v_resStartStop_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
uint8_t v_collapsed_boxed_574_; uint8_t v_clsEnabled_boxed_575_; lean_object* v_res_576_; 
v_collapsed_boxed_574_ = lean_unbox(v_collapsed_562_);
v_clsEnabled_boxed_575_ = lean_unbox(v_clsEnabled_565_);
v_res_576_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_561_, v_collapsed_boxed_574_, v_tag_563_, v_opts_564_, v_clsEnabled_boxed_575_, v_oldTraces_566_, v_msg_567_, v_resStartStop_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec_ref(v_opts_564_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_577_, uint8_t v___x_578_, lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v_x_580_);
return v___x_586_;
}
else
{
lean_object* v_head_587_; lean_object* v_tail_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_612_; 
v_head_587_ = lean_ctor_get(v_x_579_, 0);
v_tail_588_ = lean_ctor_get(v_x_579_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_x_579_);
if (v_isSharedCheck_612_ == 0)
{
v___x_590_ = v_x_579_;
v_isShared_591_ = v_isSharedCheck_612_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_tail_588_);
lean_inc(v_head_587_);
lean_dec(v_x_579_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_612_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
uint8_t v_a_593_; lean_object* v___x_599_; 
lean_inc(v_head_587_);
v___x_599_ = l_Lean_MVarId_inferInstance(v_head_587_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_dec_ref_known(v___x_599_, 1);
v_a_593_ = v___x_577_;
goto v___jp_592_;
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_611_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_611_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_611_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_611_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
uint8_t v___y_605_; uint8_t v___x_609_; 
v___x_609_ = l_Lean_Exception_isInterrupt(v_a_600_);
if (v___x_609_ == 0)
{
uint8_t v___x_610_; 
lean_inc(v_a_600_);
v___x_610_ = l_Lean_Exception_isRuntime(v_a_600_);
v___y_605_ = v___x_610_;
goto v___jp_604_;
}
else
{
v___y_605_ = v___x_609_;
goto v___jp_604_;
}
v___jp_604_:
{
if (v___y_605_ == 0)
{
lean_del_object(v___x_602_);
lean_dec(v_a_600_);
v_a_593_ = v___x_578_;
goto v___jp_592_;
}
else
{
lean_object* v___x_607_; 
lean_del_object(v___x_590_);
lean_dec(v_tail_588_);
lean_dec(v_head_587_);
lean_dec(v_x_580_);
if (v_isShared_603_ == 0)
{
v___x_607_ = v___x_602_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_600_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
v___jp_592_:
{
if (v_a_593_ == 0)
{
lean_del_object(v___x_590_);
lean_dec(v_head_587_);
v_x_579_ = v_tail_588_;
goto _start;
}
else
{
lean_object* v___x_596_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_x_580_);
v___x_596_ = v___x_590_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_head_587_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_x_580_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
v_x_579_ = v_tail_588_;
v_x_580_ = v___x_596_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v___x_613_, lean_object* v___x_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
uint8_t v___x_14415__boxed_622_; uint8_t v___x_14416__boxed_623_; lean_object* v_res_624_; 
v___x_14415__boxed_622_ = lean_unbox(v___x_613_);
v___x_14416__boxed_623_ = lean_unbox(v___x_614_);
v_res_624_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14415__boxed_622_, v___x_14416__boxed_623_, v_x_615_, v_x_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
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
lean_object* v___x_639_; 
lean_inc(v_head_634_);
v___x_639_ = l_Lean_MVarId_inferInstance(v_head_634_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_dec_ref_known(v___x_639_, 1);
lean_del_object(v___x_637_);
lean_dec(v_head_634_);
v_x_626_ = v_tail_635_;
goto _start;
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_657_; 
v_a_641_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_657_ == 0)
{
v___x_643_ = v___x_639_;
v_isShared_644_ = v_isSharedCheck_657_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_657_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
uint8_t v___y_646_; uint8_t v___x_655_; 
v___x_655_ = l_Lean_Exception_isInterrupt(v_a_641_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; 
lean_inc(v_a_641_);
v___x_656_ = l_Lean_Exception_isRuntime(v_a_641_);
v___y_646_ = v___x_656_;
goto v___jp_645_;
}
else
{
v___y_646_ = v___x_655_;
goto v___jp_645_;
}
v___jp_645_:
{
if (v___y_646_ == 0)
{
lean_del_object(v___x_643_);
lean_dec(v_a_641_);
if (v___x_625_ == 0)
{
lean_del_object(v___x_637_);
lean_dec(v_head_634_);
v_x_626_ = v_tail_635_;
goto _start;
}
else
{
lean_object* v___x_649_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_x_627_);
v___x_649_ = v___x_637_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_head_634_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_x_627_);
v___x_649_ = v_reuseFailAlloc_651_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
v_x_626_ = v_tail_635_;
v_x_627_ = v___x_649_;
goto _start;
}
}
}
else
{
lean_object* v___x_653_; 
lean_del_object(v___x_637_);
lean_dec(v_tail_635_);
lean_dec(v_head_634_);
lean_dec(v_x_627_);
if (v_isShared_644_ == 0)
{
v___x_653_ = v___x_643_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_641_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
uint8_t v___x_14497__boxed_667_; lean_object* v_res_668_; 
v___x_14497__boxed_667_ = lean_unbox(v___x_659_);
v_res_668_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14497__boxed_667_, v_x_660_, v_x_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_668_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_669_; double v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(1000000000u);
v___x_670_ = lean_float_of_nat(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(lean_object* v___x_674_, uint8_t v___x_675_, lean_object* v___x_676_, lean_object* v___f_677_, uint8_t v_transparency_678_, lean_object* v_g_679_, lean_object* v_e_680_, lean_object* v_cfg_681_, lean_object* v___x_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_options_688_; lean_object* v_inheritedTraceOptions_689_; uint8_t v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v_a_694_; lean_object* v___y_707_; uint8_t v___y_708_; lean_object* v___y_709_; lean_object* v_a_710_; uint8_t v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_727_; uint8_t v___y_728_; lean_object* v___y_729_; lean_object* v_a_730_; lean_object* v___y_740_; uint8_t v___y_741_; lean_object* v___y_742_; lean_object* v_a_743_; lean_object* v___y_746_; uint8_t v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; uint8_t v_hasTrace_759_; uint8_t v___x_760_; uint8_t v___y_762_; uint8_t v_a_870_; 
v_options_688_ = lean_ctor_get(v___y_685_, 2);
v_inheritedTraceOptions_689_ = lean_ctor_get(v___y_685_, 13);
v_hasTrace_759_ = lean_ctor_get_uint8(v_options_688_, sizeof(void*)*1);
v___x_760_ = lean_bool_not(v_hasTrace_759_);
if (v___x_760_ == 0)
{
if (v_hasTrace_759_ == 0)
{
v_a_870_ = v_hasTrace_759_;
goto v___jp_869_;
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_930_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2));
lean_inc(v___x_674_);
v___x_931_ = l_Lean_Name_append(v___x_930_, v___x_674_);
v___x_932_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_689_, v_options_688_, v___x_931_);
lean_dec(v___x_931_);
if (v___x_932_ == 0)
{
v_a_870_ = v___x_932_;
goto v___jp_869_;
}
else
{
v___y_762_ = v___x_932_;
goto v___jp_761_;
}
}
}
else
{
lean_object* v___x_933_; uint8_t v_foApprox_934_; uint8_t v_ctxApprox_935_; uint8_t v_quasiPatternApprox_936_; uint8_t v_constApprox_937_; uint8_t v_isDefEqStuckEx_938_; uint8_t v_unificationHints_939_; uint8_t v_proofIrrelevance_940_; uint8_t v_assignSyntheticOpaque_941_; uint8_t v_offsetCnstrs_942_; uint8_t v_etaStruct_943_; uint8_t v_univApprox_944_; uint8_t v_iota_945_; uint8_t v_beta_946_; uint8_t v_proj_947_; uint8_t v_zeta_948_; uint8_t v_zetaDelta_949_; uint8_t v_zetaUnused_950_; uint8_t v_zetaHave_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_989_; 
lean_dec_ref(v___f_677_);
lean_dec_ref(v___x_676_);
lean_dec(v___x_674_);
v___x_933_ = l_Lean_Meta_Context_config(v___y_683_);
v_foApprox_934_ = lean_ctor_get_uint8(v___x_933_, 0);
v_ctxApprox_935_ = lean_ctor_get_uint8(v___x_933_, 1);
v_quasiPatternApprox_936_ = lean_ctor_get_uint8(v___x_933_, 2);
v_constApprox_937_ = lean_ctor_get_uint8(v___x_933_, 3);
v_isDefEqStuckEx_938_ = lean_ctor_get_uint8(v___x_933_, 4);
v_unificationHints_939_ = lean_ctor_get_uint8(v___x_933_, 5);
v_proofIrrelevance_940_ = lean_ctor_get_uint8(v___x_933_, 6);
v_assignSyntheticOpaque_941_ = lean_ctor_get_uint8(v___x_933_, 7);
v_offsetCnstrs_942_ = lean_ctor_get_uint8(v___x_933_, 8);
v_etaStruct_943_ = lean_ctor_get_uint8(v___x_933_, 10);
v_univApprox_944_ = lean_ctor_get_uint8(v___x_933_, 11);
v_iota_945_ = lean_ctor_get_uint8(v___x_933_, 12);
v_beta_946_ = lean_ctor_get_uint8(v___x_933_, 13);
v_proj_947_ = lean_ctor_get_uint8(v___x_933_, 14);
v_zeta_948_ = lean_ctor_get_uint8(v___x_933_, 15);
v_zetaDelta_949_ = lean_ctor_get_uint8(v___x_933_, 16);
v_zetaUnused_950_ = lean_ctor_get_uint8(v___x_933_, 17);
v_zetaHave_951_ = lean_ctor_get_uint8(v___x_933_, 18);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_989_ == 0)
{
v___x_953_ = v___x_933_;
v_isShared_954_ = v_isSharedCheck_989_;
goto v_resetjp_952_;
}
else
{
lean_dec(v___x_933_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_989_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
uint8_t v_trackZetaDelta_955_; lean_object* v_zetaDeltaSet_956_; lean_object* v_lctx_957_; lean_object* v_localInstances_958_; lean_object* v_defEqCtx_x3f_959_; lean_object* v_synthPendingDepth_960_; lean_object* v_canUnfold_x3f_961_; uint8_t v_univApprox_962_; uint8_t v_inTypeClassResolution_963_; uint8_t v_cacheInferType_964_; lean_object* v_config_966_; 
v_trackZetaDelta_955_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_956_ = lean_ctor_get(v___y_683_, 1);
v_lctx_957_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_958_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_959_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_960_ = lean_ctor_get(v___y_683_, 5);
v_canUnfold_x3f_961_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_962_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_963_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_964_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
if (v_isShared_954_ == 0)
{
v_config_966_ = v___x_953_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 0, v_foApprox_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 1, v_ctxApprox_935_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 2, v_quasiPatternApprox_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 3, v_constApprox_937_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 4, v_isDefEqStuckEx_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 5, v_unificationHints_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 6, v_proofIrrelevance_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 7, v_assignSyntheticOpaque_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 8, v_offsetCnstrs_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 10, v_etaStruct_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 11, v_univApprox_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 12, v_iota_945_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 13, v_beta_946_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 14, v_proj_947_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 15, v_zeta_948_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 16, v_zetaDelta_949_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 17, v_zetaUnused_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, 18, v_zetaHave_951_);
v_config_966_ = v_reuseFailAlloc_988_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
uint64_t v___x_967_; uint64_t v___x_968_; uint64_t v___x_969_; uint64_t v___x_970_; uint64_t v___x_971_; uint64_t v_key_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_ctor_set_uint8(v_config_966_, 9, v_transparency_678_);
v___x_967_ = l_Lean_Meta_Context_configKey(v___y_683_);
v___x_968_ = 3ULL;
v___x_969_ = lean_uint64_shift_right(v___x_967_, v___x_968_);
v___x_970_ = lean_uint64_shift_left(v___x_969_, v___x_968_);
v___x_971_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_678_);
v_key_972_ = lean_uint64_lor(v___x_970_, v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_973_, 0, v_config_966_);
lean_ctor_set_uint64(v___x_973_, sizeof(void*)*1, v_key_972_);
lean_inc(v_canUnfold_x3f_961_);
lean_inc(v_synthPendingDepth_960_);
lean_inc(v_defEqCtx_x3f_959_);
lean_inc_ref(v_localInstances_958_);
lean_inc_ref(v_lctx_957_);
lean_inc(v_zetaDeltaSet_956_);
v___x_974_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v_zetaDeltaSet_956_);
lean_ctor_set(v___x_974_, 2, v_lctx_957_);
lean_ctor_set(v___x_974_, 3, v_localInstances_958_);
lean_ctor_set(v___x_974_, 4, v_defEqCtx_x3f_959_);
lean_ctor_set(v___x_974_, 5, v_synthPendingDepth_960_);
lean_ctor_set(v___x_974_, 6, v_canUnfold_x3f_961_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*7, v_trackZetaDelta_955_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*7 + 1, v_univApprox_962_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*7 + 2, v_inTypeClassResolution_963_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*7 + 3, v_cacheInferType_964_);
v___x_975_ = l_Lean_MVarId_apply(v_g_679_, v_e_680_, v_cfg_681_, v___x_682_, v___x_974_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_974_, 7);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = lean_box(0);
v___x_978_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_760_, v_a_976_, v___x_977_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_987_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_987_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = l_List_reverse___redArg(v_a_979_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
return v___x_978_;
}
}
else
{
return v___x_975_;
}
}
}
}
v___jp_690_:
{
lean_object* v___x_695_; double v___x_696_; double v___x_697_; double v___x_698_; double v___x_699_; double v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_695_ = lean_io_mono_nanos_now();
v___x_696_ = lean_float_of_nat(v___y_692_);
v___x_697_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0);
v___x_698_ = lean_float_div(v___x_696_, v___x_697_);
v___x_699_ = lean_float_of_nat(v___x_695_);
v___x_700_ = lean_float_div(v___x_699_, v___x_697_);
v___x_701_ = lean_box_float(v___x_698_);
v___x_702_ = lean_box_float(v___x_700_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_a_694_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_674_, v___x_675_, v___x_676_, v_options_688_, v___y_691_, v___y_693_, v___f_677_, v___x_704_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_705_;
}
v___jp_706_:
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v_a_710_);
v___y_691_ = v___y_708_;
v___y_692_ = v___y_707_;
v___y_693_ = v___y_709_;
v_a_694_ = v___x_711_;
goto v___jp_690_;
}
v___jp_712_:
{
if (lean_obj_tag(v___y_716_) == 0)
{
lean_object* v_a_717_; 
v_a_717_ = lean_ctor_get(v___y_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___y_716_, 1);
v___y_707_ = v___y_714_;
v___y_708_ = v___y_713_;
v___y_709_ = v___y_715_;
v_a_710_ = v_a_717_;
goto v___jp_706_;
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_a_718_ = lean_ctor_get(v___y_716_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___y_716_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___y_716_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___y_716_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 0);
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
v___y_691_ = v___y_713_;
v___y_692_ = v___y_714_;
v___y_693_ = v___y_715_;
v_a_694_ = v___x_723_;
goto v___jp_690_;
}
}
}
}
v___jp_726_:
{
lean_object* v___x_731_; double v___x_732_; double v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_731_ = lean_io_get_num_heartbeats();
v___x_732_ = lean_float_of_nat(v___y_727_);
v___x_733_ = lean_float_of_nat(v___x_731_);
v___x_734_ = lean_box_float(v___x_732_);
v___x_735_ = lean_box_float(v___x_733_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_a_730_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_674_, v___x_675_, v___x_676_, v_options_688_, v___y_728_, v___y_729_, v___f_677_, v___x_737_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_738_;
}
v___jp_739_:
{
lean_object* v___x_744_; 
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v_a_743_);
v___y_727_ = v___y_740_;
v___y_728_ = v___y_741_;
v___y_729_ = v___y_742_;
v_a_730_ = v___x_744_;
goto v___jp_726_;
}
v___jp_745_:
{
if (lean_obj_tag(v___y_749_) == 0)
{
lean_object* v_a_750_; 
v_a_750_ = lean_ctor_get(v___y_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___y_749_, 1);
v___y_740_ = v___y_746_;
v___y_741_ = v___y_747_;
v___y_742_ = v___y_748_;
v_a_743_ = v_a_750_;
goto v___jp_739_;
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_a_751_ = lean_ctor_get(v___y_749_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___y_749_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___y_749_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___y_749_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 0);
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
v___y_727_ = v___y_746_;
v___y_728_ = v___y_747_;
v___y_729_ = v___y_748_;
v_a_730_ = v___x_756_;
goto v___jp_726_;
}
}
}
}
v___jp_761_:
{
lean_object* v___x_763_; lean_object* v_a_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_763_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_686_);
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref(v___x_763_);
v___x_765_ = l_Lean_trace_profiler_useHeartbeats;
v___x_766_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_688_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v_foApprox_769_; uint8_t v_ctxApprox_770_; uint8_t v_quasiPatternApprox_771_; uint8_t v_constApprox_772_; uint8_t v_isDefEqStuckEx_773_; uint8_t v_unificationHints_774_; uint8_t v_proofIrrelevance_775_; uint8_t v_assignSyntheticOpaque_776_; uint8_t v_offsetCnstrs_777_; uint8_t v_etaStruct_778_; uint8_t v_univApprox_779_; uint8_t v_iota_780_; uint8_t v_beta_781_; uint8_t v_proj_782_; uint8_t v_zeta_783_; uint8_t v_zetaDelta_784_; uint8_t v_zetaUnused_785_; uint8_t v_zetaHave_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_817_; 
v___x_767_ = lean_io_mono_nanos_now();
v___x_768_ = l_Lean_Meta_Context_config(v___y_683_);
v_foApprox_769_ = lean_ctor_get_uint8(v___x_768_, 0);
v_ctxApprox_770_ = lean_ctor_get_uint8(v___x_768_, 1);
v_quasiPatternApprox_771_ = lean_ctor_get_uint8(v___x_768_, 2);
v_constApprox_772_ = lean_ctor_get_uint8(v___x_768_, 3);
v_isDefEqStuckEx_773_ = lean_ctor_get_uint8(v___x_768_, 4);
v_unificationHints_774_ = lean_ctor_get_uint8(v___x_768_, 5);
v_proofIrrelevance_775_ = lean_ctor_get_uint8(v___x_768_, 6);
v_assignSyntheticOpaque_776_ = lean_ctor_get_uint8(v___x_768_, 7);
v_offsetCnstrs_777_ = lean_ctor_get_uint8(v___x_768_, 8);
v_etaStruct_778_ = lean_ctor_get_uint8(v___x_768_, 10);
v_univApprox_779_ = lean_ctor_get_uint8(v___x_768_, 11);
v_iota_780_ = lean_ctor_get_uint8(v___x_768_, 12);
v_beta_781_ = lean_ctor_get_uint8(v___x_768_, 13);
v_proj_782_ = lean_ctor_get_uint8(v___x_768_, 14);
v_zeta_783_ = lean_ctor_get_uint8(v___x_768_, 15);
v_zetaDelta_784_ = lean_ctor_get_uint8(v___x_768_, 16);
v_zetaUnused_785_ = lean_ctor_get_uint8(v___x_768_, 17);
v_zetaHave_786_ = lean_ctor_get_uint8(v___x_768_, 18);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_817_ == 0)
{
v___x_788_ = v___x_768_;
v_isShared_789_ = v_isSharedCheck_817_;
goto v_resetjp_787_;
}
else
{
lean_dec(v___x_768_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_817_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
uint8_t v_trackZetaDelta_790_; lean_object* v_zetaDeltaSet_791_; lean_object* v_lctx_792_; lean_object* v_localInstances_793_; lean_object* v_defEqCtx_x3f_794_; lean_object* v_synthPendingDepth_795_; lean_object* v_canUnfold_x3f_796_; uint8_t v_univApprox_797_; uint8_t v_inTypeClassResolution_798_; uint8_t v_cacheInferType_799_; lean_object* v_config_801_; 
v_trackZetaDelta_790_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_791_ = lean_ctor_get(v___y_683_, 1);
v_lctx_792_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_793_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_794_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_795_ = lean_ctor_get(v___y_683_, 5);
v_canUnfold_x3f_796_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_797_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_798_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_799_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
if (v_isShared_789_ == 0)
{
v_config_801_ = v___x_788_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 0, v_foApprox_769_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 1, v_ctxApprox_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 2, v_quasiPatternApprox_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 3, v_constApprox_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 4, v_isDefEqStuckEx_773_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 5, v_unificationHints_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 6, v_proofIrrelevance_775_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 7, v_assignSyntheticOpaque_776_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 8, v_offsetCnstrs_777_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 10, v_etaStruct_778_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 11, v_univApprox_779_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 12, v_iota_780_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 13, v_beta_781_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 14, v_proj_782_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 15, v_zeta_783_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 16, v_zetaDelta_784_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 17, v_zetaUnused_785_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, 18, v_zetaHave_786_);
v_config_801_ = v_reuseFailAlloc_816_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
uint64_t v___x_802_; uint64_t v___x_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v_key_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_ctor_set_uint8(v_config_801_, 9, v_transparency_678_);
v___x_802_ = l_Lean_Meta_Context_configKey(v___y_683_);
v___x_803_ = 3ULL;
v___x_804_ = lean_uint64_shift_right(v___x_802_, v___x_803_);
v___x_805_ = lean_uint64_shift_left(v___x_804_, v___x_803_);
v___x_806_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_678_);
v_key_807_ = lean_uint64_lor(v___x_805_, v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_808_, 0, v_config_801_);
lean_ctor_set_uint64(v___x_808_, sizeof(void*)*1, v_key_807_);
lean_inc(v_canUnfold_x3f_796_);
lean_inc(v_synthPendingDepth_795_);
lean_inc(v_defEqCtx_x3f_794_);
lean_inc_ref(v_localInstances_793_);
lean_inc_ref(v_lctx_792_);
lean_inc(v_zetaDeltaSet_791_);
v___x_809_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v_zetaDeltaSet_791_);
lean_ctor_set(v___x_809_, 2, v_lctx_792_);
lean_ctor_set(v___x_809_, 3, v_localInstances_793_);
lean_ctor_set(v___x_809_, 4, v_defEqCtx_x3f_794_);
lean_ctor_set(v___x_809_, 5, v_synthPendingDepth_795_);
lean_ctor_set(v___x_809_, 6, v_canUnfold_x3f_796_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*7, v_trackZetaDelta_790_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*7 + 1, v_univApprox_797_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*7 + 2, v_inTypeClassResolution_798_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*7 + 3, v_cacheInferType_799_);
v___x_810_ = l_Lean_MVarId_apply(v_g_679_, v_e_680_, v_cfg_681_, v___x_682_, v___x_809_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_809_, 7);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v___x_812_ = lean_box(0);
v___x_813_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_766_, v_a_811_, v___x_812_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_815_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_813_, 1);
v___x_815_ = l_List_reverse___redArg(v_a_814_);
v___y_707_ = v___x_767_;
v___y_708_ = v___y_762_;
v___y_709_ = v_a_764_;
v_a_710_ = v___x_815_;
goto v___jp_706_;
}
else
{
v___y_713_ = v___y_762_;
v___y_714_ = v___x_767_;
v___y_715_ = v_a_764_;
v___y_716_ = v___x_813_;
goto v___jp_712_;
}
}
else
{
v___y_713_ = v___y_762_;
v___y_714_ = v___x_767_;
v___y_715_ = v_a_764_;
v___y_716_ = v___x_810_;
goto v___jp_712_;
}
}
}
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v_foApprox_820_; uint8_t v_ctxApprox_821_; uint8_t v_quasiPatternApprox_822_; uint8_t v_constApprox_823_; uint8_t v_isDefEqStuckEx_824_; uint8_t v_unificationHints_825_; uint8_t v_proofIrrelevance_826_; uint8_t v_assignSyntheticOpaque_827_; uint8_t v_offsetCnstrs_828_; uint8_t v_etaStruct_829_; uint8_t v_univApprox_830_; uint8_t v_iota_831_; uint8_t v_beta_832_; uint8_t v_proj_833_; uint8_t v_zeta_834_; uint8_t v_zetaDelta_835_; uint8_t v_zetaUnused_836_; uint8_t v_zetaHave_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_868_; 
v___x_818_ = lean_io_get_num_heartbeats();
v___x_819_ = l_Lean_Meta_Context_config(v___y_683_);
v_foApprox_820_ = lean_ctor_get_uint8(v___x_819_, 0);
v_ctxApprox_821_ = lean_ctor_get_uint8(v___x_819_, 1);
v_quasiPatternApprox_822_ = lean_ctor_get_uint8(v___x_819_, 2);
v_constApprox_823_ = lean_ctor_get_uint8(v___x_819_, 3);
v_isDefEqStuckEx_824_ = lean_ctor_get_uint8(v___x_819_, 4);
v_unificationHints_825_ = lean_ctor_get_uint8(v___x_819_, 5);
v_proofIrrelevance_826_ = lean_ctor_get_uint8(v___x_819_, 6);
v_assignSyntheticOpaque_827_ = lean_ctor_get_uint8(v___x_819_, 7);
v_offsetCnstrs_828_ = lean_ctor_get_uint8(v___x_819_, 8);
v_etaStruct_829_ = lean_ctor_get_uint8(v___x_819_, 10);
v_univApprox_830_ = lean_ctor_get_uint8(v___x_819_, 11);
v_iota_831_ = lean_ctor_get_uint8(v___x_819_, 12);
v_beta_832_ = lean_ctor_get_uint8(v___x_819_, 13);
v_proj_833_ = lean_ctor_get_uint8(v___x_819_, 14);
v_zeta_834_ = lean_ctor_get_uint8(v___x_819_, 15);
v_zetaDelta_835_ = lean_ctor_get_uint8(v___x_819_, 16);
v_zetaUnused_836_ = lean_ctor_get_uint8(v___x_819_, 17);
v_zetaHave_837_ = lean_ctor_get_uint8(v___x_819_, 18);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_868_ == 0)
{
v___x_839_ = v___x_819_;
v_isShared_840_ = v_isSharedCheck_868_;
goto v_resetjp_838_;
}
else
{
lean_dec(v___x_819_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_868_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
uint8_t v_trackZetaDelta_841_; lean_object* v_zetaDeltaSet_842_; lean_object* v_lctx_843_; lean_object* v_localInstances_844_; lean_object* v_defEqCtx_x3f_845_; lean_object* v_synthPendingDepth_846_; lean_object* v_canUnfold_x3f_847_; uint8_t v_univApprox_848_; uint8_t v_inTypeClassResolution_849_; uint8_t v_cacheInferType_850_; lean_object* v_config_852_; 
v_trackZetaDelta_841_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_842_ = lean_ctor_get(v___y_683_, 1);
v_lctx_843_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_844_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_845_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_846_ = lean_ctor_get(v___y_683_, 5);
v_canUnfold_x3f_847_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_848_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_849_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_850_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
if (v_isShared_840_ == 0)
{
v_config_852_ = v___x_839_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 0, v_foApprox_820_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 1, v_ctxApprox_821_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 2, v_quasiPatternApprox_822_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 3, v_constApprox_823_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 4, v_isDefEqStuckEx_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 5, v_unificationHints_825_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 6, v_proofIrrelevance_826_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 7, v_assignSyntheticOpaque_827_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 8, v_offsetCnstrs_828_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 10, v_etaStruct_829_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 11, v_univApprox_830_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 12, v_iota_831_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 13, v_beta_832_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 14, v_proj_833_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 15, v_zeta_834_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 16, v_zetaDelta_835_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 17, v_zetaUnused_836_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, 18, v_zetaHave_837_);
v_config_852_ = v_reuseFailAlloc_867_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
uint64_t v___x_853_; uint64_t v___x_854_; uint64_t v___x_855_; uint64_t v___x_856_; uint64_t v___x_857_; uint64_t v_key_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_ctor_set_uint8(v_config_852_, 9, v_transparency_678_);
v___x_853_ = l_Lean_Meta_Context_configKey(v___y_683_);
v___x_854_ = 3ULL;
v___x_855_ = lean_uint64_shift_right(v___x_853_, v___x_854_);
v___x_856_ = lean_uint64_shift_left(v___x_855_, v___x_854_);
v___x_857_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_678_);
v_key_858_ = lean_uint64_lor(v___x_856_, v___x_857_);
v___x_859_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_859_, 0, v_config_852_);
lean_ctor_set_uint64(v___x_859_, sizeof(void*)*1, v_key_858_);
lean_inc(v_canUnfold_x3f_847_);
lean_inc(v_synthPendingDepth_846_);
lean_inc(v_defEqCtx_x3f_845_);
lean_inc_ref(v_localInstances_844_);
lean_inc_ref(v_lctx_843_);
lean_inc(v_zetaDeltaSet_842_);
v___x_860_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v_zetaDeltaSet_842_);
lean_ctor_set(v___x_860_, 2, v_lctx_843_);
lean_ctor_set(v___x_860_, 3, v_localInstances_844_);
lean_ctor_set(v___x_860_, 4, v_defEqCtx_x3f_845_);
lean_ctor_set(v___x_860_, 5, v_synthPendingDepth_846_);
lean_ctor_set(v___x_860_, 6, v_canUnfold_x3f_847_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*7, v_trackZetaDelta_841_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*7 + 1, v_univApprox_848_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*7 + 2, v_inTypeClassResolution_849_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*7 + 3, v_cacheInferType_850_);
v___x_861_ = l_Lean_MVarId_apply(v_g_679_, v_e_680_, v_cfg_681_, v___x_682_, v___x_860_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_860_, 7);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 1);
v___x_863_ = lean_box(0);
v___x_864_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_760_, v___x_766_, v_a_862_, v___x_863_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_866_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
v___x_866_ = l_List_reverse___redArg(v_a_865_);
v___y_740_ = v___x_818_;
v___y_741_ = v___y_762_;
v___y_742_ = v_a_764_;
v_a_743_ = v___x_866_;
goto v___jp_739_;
}
else
{
v___y_746_ = v___x_818_;
v___y_747_ = v___y_762_;
v___y_748_ = v_a_764_;
v___y_749_ = v___x_864_;
goto v___jp_745_;
}
}
else
{
v___y_746_ = v___x_818_;
v___y_747_ = v___y_762_;
v___y_748_ = v_a_764_;
v___y_749_ = v___x_861_;
goto v___jp_745_;
}
}
}
}
}
v___jp_869_:
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = l_Lean_trace_profiler;
v___x_872_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_688_, v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; uint8_t v_foApprox_874_; uint8_t v_ctxApprox_875_; uint8_t v_quasiPatternApprox_876_; uint8_t v_constApprox_877_; uint8_t v_isDefEqStuckEx_878_; uint8_t v_unificationHints_879_; uint8_t v_proofIrrelevance_880_; uint8_t v_assignSyntheticOpaque_881_; uint8_t v_offsetCnstrs_882_; uint8_t v_etaStruct_883_; uint8_t v_univApprox_884_; uint8_t v_iota_885_; uint8_t v_beta_886_; uint8_t v_proj_887_; uint8_t v_zeta_888_; uint8_t v_zetaDelta_889_; uint8_t v_zetaUnused_890_; uint8_t v_zetaHave_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_929_; 
lean_dec_ref(v___f_677_);
lean_dec_ref(v___x_676_);
lean_dec(v___x_674_);
v___x_873_ = l_Lean_Meta_Context_config(v___y_683_);
v_foApprox_874_ = lean_ctor_get_uint8(v___x_873_, 0);
v_ctxApprox_875_ = lean_ctor_get_uint8(v___x_873_, 1);
v_quasiPatternApprox_876_ = lean_ctor_get_uint8(v___x_873_, 2);
v_constApprox_877_ = lean_ctor_get_uint8(v___x_873_, 3);
v_isDefEqStuckEx_878_ = lean_ctor_get_uint8(v___x_873_, 4);
v_unificationHints_879_ = lean_ctor_get_uint8(v___x_873_, 5);
v_proofIrrelevance_880_ = lean_ctor_get_uint8(v___x_873_, 6);
v_assignSyntheticOpaque_881_ = lean_ctor_get_uint8(v___x_873_, 7);
v_offsetCnstrs_882_ = lean_ctor_get_uint8(v___x_873_, 8);
v_etaStruct_883_ = lean_ctor_get_uint8(v___x_873_, 10);
v_univApprox_884_ = lean_ctor_get_uint8(v___x_873_, 11);
v_iota_885_ = lean_ctor_get_uint8(v___x_873_, 12);
v_beta_886_ = lean_ctor_get_uint8(v___x_873_, 13);
v_proj_887_ = lean_ctor_get_uint8(v___x_873_, 14);
v_zeta_888_ = lean_ctor_get_uint8(v___x_873_, 15);
v_zetaDelta_889_ = lean_ctor_get_uint8(v___x_873_, 16);
v_zetaUnused_890_ = lean_ctor_get_uint8(v___x_873_, 17);
v_zetaHave_891_ = lean_ctor_get_uint8(v___x_873_, 18);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_929_ == 0)
{
v___x_893_ = v___x_873_;
v_isShared_894_ = v_isSharedCheck_929_;
goto v_resetjp_892_;
}
else
{
lean_dec(v___x_873_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_929_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
uint8_t v_trackZetaDelta_895_; lean_object* v_zetaDeltaSet_896_; lean_object* v_lctx_897_; lean_object* v_localInstances_898_; lean_object* v_defEqCtx_x3f_899_; lean_object* v_synthPendingDepth_900_; lean_object* v_canUnfold_x3f_901_; uint8_t v_univApprox_902_; uint8_t v_inTypeClassResolution_903_; uint8_t v_cacheInferType_904_; lean_object* v_config_906_; 
v_trackZetaDelta_895_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_896_ = lean_ctor_get(v___y_683_, 1);
v_lctx_897_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_898_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_899_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_900_ = lean_ctor_get(v___y_683_, 5);
v_canUnfold_x3f_901_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_902_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_903_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_904_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
if (v_isShared_894_ == 0)
{
v_config_906_ = v___x_893_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 0, v_foApprox_874_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 1, v_ctxApprox_875_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 2, v_quasiPatternApprox_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 3, v_constApprox_877_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 4, v_isDefEqStuckEx_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 5, v_unificationHints_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 6, v_proofIrrelevance_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 7, v_assignSyntheticOpaque_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 8, v_offsetCnstrs_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 10, v_etaStruct_883_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 11, v_univApprox_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 12, v_iota_885_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 13, v_beta_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 14, v_proj_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 15, v_zeta_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 16, v_zetaDelta_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 17, v_zetaUnused_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, 18, v_zetaHave_891_);
v_config_906_ = v_reuseFailAlloc_928_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v___x_910_; uint64_t v___x_911_; uint64_t v_key_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_ctor_set_uint8(v_config_906_, 9, v_transparency_678_);
v___x_907_ = l_Lean_Meta_Context_configKey(v___y_683_);
v___x_908_ = 3ULL;
v___x_909_ = lean_uint64_shift_right(v___x_907_, v___x_908_);
v___x_910_ = lean_uint64_shift_left(v___x_909_, v___x_908_);
v___x_911_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_678_);
v_key_912_ = lean_uint64_lor(v___x_910_, v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_913_, 0, v_config_906_);
lean_ctor_set_uint64(v___x_913_, sizeof(void*)*1, v_key_912_);
lean_inc(v_canUnfold_x3f_901_);
lean_inc(v_synthPendingDepth_900_);
lean_inc(v_defEqCtx_x3f_899_);
lean_inc_ref(v_localInstances_898_);
lean_inc_ref(v_lctx_897_);
lean_inc(v_zetaDeltaSet_896_);
v___x_914_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v_zetaDeltaSet_896_);
lean_ctor_set(v___x_914_, 2, v_lctx_897_);
lean_ctor_set(v___x_914_, 3, v_localInstances_898_);
lean_ctor_set(v___x_914_, 4, v_defEqCtx_x3f_899_);
lean_ctor_set(v___x_914_, 5, v_synthPendingDepth_900_);
lean_ctor_set(v___x_914_, 6, v_canUnfold_x3f_901_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*7, v_trackZetaDelta_895_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*7 + 1, v_univApprox_902_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*7 + 2, v_inTypeClassResolution_903_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*7 + 3, v_cacheInferType_904_);
v___x_915_ = l_Lean_MVarId_apply(v_g_679_, v_e_680_, v_cfg_681_, v___x_682_, v___x_914_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_914_, 7);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = lean_box(0);
v___x_918_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_872_, v_a_916_, v___x_917_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_927_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_927_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = l_List_reverse___redArg(v_a_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_923_);
v___x_925_ = v___x_921_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
else
{
return v___x_918_;
}
}
else
{
return v___x_915_;
}
}
}
}
else
{
v___y_762_ = v_a_870_;
goto v___jp_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v___x_990_, lean_object* v___x_991_, lean_object* v___x_992_, lean_object* v___f_993_, lean_object* v_transparency_994_, lean_object* v_g_995_, lean_object* v_e_996_, lean_object* v_cfg_997_, lean_object* v___x_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
uint8_t v___x_14585__boxed_1004_; uint8_t v_transparency_boxed_1005_; lean_object* v_res_1006_; 
v___x_14585__boxed_1004_ = lean_unbox(v___x_991_);
v_transparency_boxed_1005_ = lean_unbox(v_transparency_994_);
v_res_1006_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v___x_990_, v___x_14585__boxed_1004_, v___x_992_, v___f_993_, v_transparency_boxed_1005_, v_g_995_, v_e_996_, v_cfg_997_, v___x_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_1008_, lean_object* v_g_1009_, lean_object* v_cfg_1010_, lean_object* v_e_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___f_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___f_1024_; lean_object* v___x_1025_; 
lean_inc_ref(v_e_1011_);
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1017_, 0, v_e_1011_);
v___x_1018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_1019_ = lean_box(0);
v___x_1020_ = 1;
v___x_1021_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_1022_ = lean_box(v___x_1020_);
v___x_1023_ = lean_box(v_transparency_1008_);
v___f_1024_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_1024_, 0, v___x_1018_);
lean_closure_set(v___f_1024_, 1, v___x_1022_);
lean_closure_set(v___f_1024_, 2, v___x_1021_);
lean_closure_set(v___f_1024_, 3, v___f_1017_);
lean_closure_set(v___f_1024_, 4, v___x_1023_);
lean_closure_set(v___f_1024_, 5, v_g_1009_);
lean_closure_set(v___f_1024_, 6, v_e_1011_);
lean_closure_set(v___f_1024_, 7, v_cfg_1010_);
lean_closure_set(v___f_1024_, 8, v___x_1019_);
v___x_1025_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_1024_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_1026_, lean_object* v_g_1027_, lean_object* v_cfg_1028_, lean_object* v_e_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
uint8_t v_transparency_boxed_1035_; lean_object* v_res_1036_; 
v_transparency_boxed_1035_ = lean_unbox(v_transparency_1026_);
v_res_1036_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_1035_, v_g_1027_, v_cfg_1028_, v_e_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_1037_, uint8_t v_transparency_1038_, lean_object* v_lemmas_1039_, lean_object* v_g_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_1039_, v_a_1041_, v_a_1042_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1055_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1055_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1055_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1049_ = lean_box(v_transparency_1038_);
v___f_1050_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1050_, 0, v___x_1049_);
lean_closure_set(v___f_1050_, 1, v_g_1040_);
lean_closure_set(v___f_1050_, 2, v_cfg_1037_);
v___x_1051_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_1051_, 0, lean_box(0));
lean_closure_set(v___x_1051_, 1, lean_box(0));
lean_closure_set(v___x_1051_, 2, v___f_1050_);
lean_closure_set(v___x_1051_, 3, v_a_1045_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1051_);
v___x_1053_ = v___x_1047_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v_g_1040_);
lean_dec_ref(v_cfg_1037_);
v_a_1056_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1044_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1044_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_1064_, lean_object* v_transparency_1065_, lean_object* v_lemmas_1066_, lean_object* v_g_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
uint8_t v_transparency_boxed_1071_; lean_object* v_res_1072_; 
v_transparency_boxed_1071_ = lean_unbox(v_transparency_1065_);
v_res_1072_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1064_, v_transparency_boxed_1071_, v_lemmas_1066_, v_g_1067_, v_a_1068_, v_a_1069_);
lean_dec(v_a_1069_);
lean_dec(v_a_1068_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_1073_, uint8_t v_transparency_1074_, lean_object* v_lemmas_1075_, lean_object* v_g_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1073_, v_transparency_1074_, v_lemmas_1075_, v_g_1076_, v_a_1078_, v_a_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_1083_, lean_object* v_transparency_1084_, lean_object* v_lemmas_1085_, lean_object* v_g_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
uint8_t v_transparency_boxed_1092_; lean_object* v_res_1093_; 
v_transparency_boxed_1092_ = lean_unbox(v_transparency_1084_);
v_res_1093_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_1083_, v_transparency_boxed_1092_, v_lemmas_1085_, v_g_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_00_u03b1_1094_, lean_object* v_x_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_1095_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1102_, lean_object* v_x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_00_u03b1_1102_, v_x_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1110_, uint8_t v_transparency_1111_, lean_object* v_lemmas_1112_, lean_object* v_g_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1110_, v_transparency_1111_, v_lemmas_1112_, v_g_1113_, v_a_1115_, v_a_1117_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = l_Lean_Meta_Iterator_head___redArg(v_a_1120_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
return v___x_1121_;
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_a_1122_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1119_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1119_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1130_, lean_object* v_transparency_1131_, lean_object* v_lemmas_1132_, lean_object* v_g_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
uint8_t v_transparency_boxed_1139_; lean_object* v_res_1140_; 
v_transparency_boxed_1139_ = lean_unbox(v_transparency_1131_);
v_res_1140_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1130_, v_transparency_boxed_1139_, v_lemmas_1132_, v_g_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1141_){
_start:
{
lean_object* v_toApplyRulesConfig_1142_; lean_object* v_toBacktrackConfig_1143_; 
v_toApplyRulesConfig_1142_ = lean_ctor_get(v_x_1141_, 0);
v_toBacktrackConfig_1143_ = lean_ctor_get(v_toApplyRulesConfig_1142_, 0);
lean_inc_ref(v_toBacktrackConfig_1143_);
return v_toBacktrackConfig_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1144_);
lean_dec_ref(v_x_1144_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1148_, lean_object* v_discharge_1149_, lean_object* v_g_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; 
lean_inc(v___y_1154_);
lean_inc_ref(v___y_1153_);
lean_inc(v___y_1152_);
lean_inc_ref(v___y_1151_);
lean_inc(v_g_1150_);
v___x_1156_ = lean_apply_6(v_test_1148_, v_g_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, lean_box(0));
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1167_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1167_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1167_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_unbox(v_a_1157_);
lean_dec(v_a_1157_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; 
lean_del_object(v___x_1159_);
lean_inc(v___y_1154_);
lean_inc_ref(v___y_1153_);
lean_inc(v___y_1152_);
lean_inc_ref(v___y_1151_);
v___x_1162_ = lean_apply_6(v_discharge_1149_, v_g_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, lean_box(0));
return v___x_1162_;
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_dec(v_g_1150_);
lean_dec_ref(v_discharge_1149_);
v___x_1163_ = lean_box(0);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1163_);
v___x_1165_ = v___x_1159_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
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
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec(v_g_1150_);
lean_dec_ref(v_discharge_1149_);
v_a_1168_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1156_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1156_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1176_, lean_object* v_discharge_1177_, lean_object* v_g_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1176_, v_discharge_1177_, v_g_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1185_, lean_object* v_test_1186_){
_start:
{
lean_object* v_toApplyRulesConfig_1187_; lean_object* v_toBacktrackConfig_1188_; uint8_t v_backtracking_1189_; uint8_t v_intro_1190_; uint8_t v_constructor_1191_; uint8_t v_suggestions_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1224_; 
v_toApplyRulesConfig_1187_ = lean_ctor_get(v_cfg_1185_, 0);
lean_inc_ref(v_toApplyRulesConfig_1187_);
v_toBacktrackConfig_1188_ = lean_ctor_get(v_toApplyRulesConfig_1187_, 0);
lean_inc_ref(v_toBacktrackConfig_1188_);
v_backtracking_1189_ = lean_ctor_get_uint8(v_cfg_1185_, sizeof(void*)*1);
v_intro_1190_ = lean_ctor_get_uint8(v_cfg_1185_, sizeof(void*)*1 + 1);
v_constructor_1191_ = lean_ctor_get_uint8(v_cfg_1185_, sizeof(void*)*1 + 2);
v_suggestions_1192_ = lean_ctor_get_uint8(v_cfg_1185_, sizeof(void*)*1 + 3);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_cfg_1185_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v_cfg_1185_, 0);
lean_dec(v_unused_1225_);
v___x_1194_ = v_cfg_1185_;
v_isShared_1195_ = v_isSharedCheck_1224_;
goto v_resetjp_1193_;
}
else
{
lean_dec(v_cfg_1185_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1224_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_toApplyConfig_1196_; uint8_t v_transparency_1197_; uint8_t v_symm_1198_; uint8_t v_exfalso_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1222_; 
v_toApplyConfig_1196_ = lean_ctor_get(v_toApplyRulesConfig_1187_, 1);
v_transparency_1197_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1187_, sizeof(void*)*2);
v_symm_1198_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1187_, sizeof(void*)*2 + 1);
v_exfalso_1199_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1187_, sizeof(void*)*2 + 2);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_toApplyRulesConfig_1187_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_toApplyRulesConfig_1187_, 0);
lean_dec(v_unused_1223_);
v___x_1201_ = v_toApplyRulesConfig_1187_;
v_isShared_1202_ = v_isSharedCheck_1222_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_toApplyConfig_1196_);
lean_dec(v_toApplyRulesConfig_1187_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1222_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_maxDepth_1203_; lean_object* v_proc_1204_; lean_object* v_suspend_1205_; lean_object* v_discharge_1206_; uint8_t v_commitIndependentGoals_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1221_; 
v_maxDepth_1203_ = lean_ctor_get(v_toBacktrackConfig_1188_, 0);
v_proc_1204_ = lean_ctor_get(v_toBacktrackConfig_1188_, 1);
v_suspend_1205_ = lean_ctor_get(v_toBacktrackConfig_1188_, 2);
v_discharge_1206_ = lean_ctor_get(v_toBacktrackConfig_1188_, 3);
v_commitIndependentGoals_1207_ = lean_ctor_get_uint8(v_toBacktrackConfig_1188_, sizeof(void*)*4);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_toBacktrackConfig_1188_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1209_ = v_toBacktrackConfig_1188_;
v_isShared_1210_ = v_isSharedCheck_1221_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_discharge_1206_);
lean_inc(v_suspend_1205_);
lean_inc(v_proc_1204_);
lean_inc(v_maxDepth_1203_);
lean_dec(v_toBacktrackConfig_1188_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1221_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___f_1211_; lean_object* v___x_1213_; 
v___f_1211_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1211_, 0, v_test_1186_);
lean_closure_set(v___f_1211_, 1, v_discharge_1206_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 3, v___f_1211_);
v___x_1213_ = v___x_1209_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_maxDepth_1203_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_proc_1204_);
lean_ctor_set(v_reuseFailAlloc_1220_, 2, v_suspend_1205_);
lean_ctor_set(v_reuseFailAlloc_1220_, 3, v___f_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1220_, sizeof(void*)*4, v_commitIndependentGoals_1207_);
v___x_1213_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1213_);
v___x_1215_ = v___x_1201_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_toApplyConfig_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1219_, sizeof(void*)*2, v_transparency_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1219_, sizeof(void*)*2 + 1, v_symm_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1219_, sizeof(void*)*2 + 2, v_exfalso_1199_);
v___x_1215_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1217_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1215_);
v___x_1217_ = v___x_1194_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
lean_ctor_set_uint8(v_reuseFailAlloc_1218_, sizeof(void*)*1, v_backtracking_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1218_, sizeof(void*)*1 + 1, v_intro_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1218_, sizeof(void*)*1 + 2, v_constructor_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1218_, sizeof(void*)*1 + 3, v_suggestions_1192_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1226_, lean_object* v_proc_1227_, lean_object* v_orig_1228_, lean_object* v_goals_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
if (lean_obj_tag(v_goals_1229_) == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref(v_proc_1227_);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
v___x_1235_ = lean_apply_7(v_proc_1226_, v_orig_1228_, v_goals_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, lean_box(0));
return v___x_1235_;
}
else
{
lean_object* v_head_1236_; lean_object* v_tail_1237_; lean_object* v___x_1238_; 
v_head_1236_ = lean_ctor_get(v_goals_1229_, 0);
v_tail_1237_ = lean_ctor_get(v_goals_1229_, 1);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
lean_inc(v_head_1236_);
v___x_1238_ = lean_apply_6(v_proc_1227_, v_head_1236_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, lean_box(0));
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1248_; 
lean_inc(v_tail_1237_);
lean_dec_ref_known(v_goals_1229_, 2);
lean_dec(v_orig_1228_);
lean_dec_ref(v_proc_1226_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1248_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1248_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1243_ = l_List_appendTR___redArg(v_a_1239_, v_tail_1237_);
v___x_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1244_);
v___x_1246_ = v___x_1241_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1261_; 
v_a_1249_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1251_ = v___x_1238_;
v_isShared_1252_ = v_isSharedCheck_1261_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1238_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1261_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
uint8_t v___y_1254_; uint8_t v___x_1259_; 
v___x_1259_ = l_Lean_Exception_isInterrupt(v_a_1249_);
if (v___x_1259_ == 0)
{
uint8_t v___x_1260_; 
lean_inc(v_a_1249_);
v___x_1260_ = l_Lean_Exception_isRuntime(v_a_1249_);
v___y_1254_ = v___x_1260_;
goto v___jp_1253_;
}
else
{
v___y_1254_ = v___x_1259_;
goto v___jp_1253_;
}
v___jp_1253_:
{
if (v___y_1254_ == 0)
{
lean_object* v___x_1255_; 
lean_del_object(v___x_1251_);
lean_dec(v_a_1249_);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
v___x_1255_ = lean_apply_7(v_proc_1226_, v_orig_1228_, v_goals_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, lean_box(0));
return v___x_1255_;
}
else
{
lean_object* v___x_1257_; 
lean_dec_ref_known(v_goals_1229_, 2);
lean_dec(v_orig_1228_);
lean_dec_ref(v_proc_1226_);
if (v_isShared_1252_ == 0)
{
v___x_1257_ = v___x_1251_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1249_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1262_, lean_object* v_proc_1263_, lean_object* v_orig_1264_, lean_object* v_goals_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1262_, v_proc_1263_, v_orig_1264_, v_goals_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1272_, lean_object* v_proc_1273_){
_start:
{
lean_object* v_toApplyRulesConfig_1274_; lean_object* v_toBacktrackConfig_1275_; uint8_t v_backtracking_1276_; uint8_t v_intro_1277_; uint8_t v_constructor_1278_; uint8_t v_suggestions_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1311_; 
v_toApplyRulesConfig_1274_ = lean_ctor_get(v_cfg_1272_, 0);
lean_inc_ref(v_toApplyRulesConfig_1274_);
v_toBacktrackConfig_1275_ = lean_ctor_get(v_toApplyRulesConfig_1274_, 0);
lean_inc_ref(v_toBacktrackConfig_1275_);
v_backtracking_1276_ = lean_ctor_get_uint8(v_cfg_1272_, sizeof(void*)*1);
v_intro_1277_ = lean_ctor_get_uint8(v_cfg_1272_, sizeof(void*)*1 + 1);
v_constructor_1278_ = lean_ctor_get_uint8(v_cfg_1272_, sizeof(void*)*1 + 2);
v_suggestions_1279_ = lean_ctor_get_uint8(v_cfg_1272_, sizeof(void*)*1 + 3);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_cfg_1272_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v_cfg_1272_, 0);
lean_dec(v_unused_1312_);
v___x_1281_ = v_cfg_1272_;
v_isShared_1282_ = v_isSharedCheck_1311_;
goto v_resetjp_1280_;
}
else
{
lean_dec(v_cfg_1272_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1311_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_toApplyConfig_1283_; uint8_t v_transparency_1284_; uint8_t v_symm_1285_; uint8_t v_exfalso_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1309_; 
v_toApplyConfig_1283_ = lean_ctor_get(v_toApplyRulesConfig_1274_, 1);
v_transparency_1284_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1274_, sizeof(void*)*2);
v_symm_1285_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1274_, sizeof(void*)*2 + 1);
v_exfalso_1286_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1274_, sizeof(void*)*2 + 2);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_toApplyRulesConfig_1274_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v_toApplyRulesConfig_1274_, 0);
lean_dec(v_unused_1310_);
v___x_1288_ = v_toApplyRulesConfig_1274_;
v_isShared_1289_ = v_isSharedCheck_1309_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_toApplyConfig_1283_);
lean_dec(v_toApplyRulesConfig_1274_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1309_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_maxDepth_1290_; lean_object* v_proc_1291_; lean_object* v_suspend_1292_; lean_object* v_discharge_1293_; uint8_t v_commitIndependentGoals_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1308_; 
v_maxDepth_1290_ = lean_ctor_get(v_toBacktrackConfig_1275_, 0);
v_proc_1291_ = lean_ctor_get(v_toBacktrackConfig_1275_, 1);
v_suspend_1292_ = lean_ctor_get(v_toBacktrackConfig_1275_, 2);
v_discharge_1293_ = lean_ctor_get(v_toBacktrackConfig_1275_, 3);
v_commitIndependentGoals_1294_ = lean_ctor_get_uint8(v_toBacktrackConfig_1275_, sizeof(void*)*4);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_toBacktrackConfig_1275_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1296_ = v_toBacktrackConfig_1275_;
v_isShared_1297_ = v_isSharedCheck_1308_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_discharge_1293_);
lean_inc(v_suspend_1292_);
lean_inc(v_proc_1291_);
lean_inc(v_maxDepth_1290_);
lean_dec(v_toBacktrackConfig_1275_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1308_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___f_1298_; lean_object* v___x_1300_; 
v___f_1298_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1298_, 0, v_proc_1291_);
lean_closure_set(v___f_1298_, 1, v_proc_1273_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 1, v___f_1298_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_maxDepth_1290_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v___f_1298_);
lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_suspend_1292_);
lean_ctor_set(v_reuseFailAlloc_1307_, 3, v_discharge_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*4, v_commitIndependentGoals_1294_);
v___x_1300_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1302_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1300_);
v___x_1302_ = v___x_1288_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_toApplyConfig_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1306_, sizeof(void*)*2, v_transparency_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1306_, sizeof(void*)*2 + 1, v_symm_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1306_, sizeof(void*)*2 + 2, v_exfalso_1286_);
v___x_1302_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1304_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1302_);
v___x_1304_ = v___x_1281_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*1, v_backtracking_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*1 + 1, v_intro_1277_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*1 + 2, v_constructor_1278_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*1 + 3, v_suggestions_1279_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = 1;
v___x_1320_ = l_Lean_Meta_intro1Core(v_g_1313_, v___x_1319_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1338_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1338_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1338_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_snd_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1336_; 
v_snd_1325_ = lean_ctor_get(v_a_1321_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_a_1321_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v_a_1321_, 0);
lean_dec(v_unused_1337_);
v___x_1327_ = v_a_1321_;
v_isShared_1328_ = v_isSharedCheck_1336_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_snd_1325_);
lean_dec(v_a_1321_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1336_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = lean_box(0);
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 1);
lean_ctor_set(v___x_1327_, 1, v___x_1329_);
lean_ctor_set(v___x_1327_, 0, v_snd_1325_);
v___x_1331_ = v___x_1327_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_snd_1325_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1333_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1331_);
v___x_1333_ = v___x_1323_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
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
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
v_a_1339_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1320_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1320_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1355_){
_start:
{
lean_object* v___f_1356_; lean_object* v___x_1357_; 
v___f_1356_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1357_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1355_, v___f_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_){
_start:
{
lean_object* v_ks_1362_; lean_object* v_vs_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1387_; 
v_ks_1362_ = lean_ctor_get(v_x_1358_, 0);
v_vs_1363_ = lean_ctor_get(v_x_1358_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_x_1358_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1365_ = v_x_1358_;
v_isShared_1366_ = v_isSharedCheck_1387_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_vs_1363_);
lean_inc(v_ks_1362_);
lean_dec(v_x_1358_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1387_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = lean_array_get_size(v_ks_1362_);
v___x_1368_ = lean_nat_dec_lt(v_x_1359_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_dec(v_x_1359_);
v___x_1369_ = lean_array_push(v_ks_1362_, v_x_1360_);
v___x_1370_ = lean_array_push(v_vs_1363_, v_x_1361_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___x_1370_);
lean_ctor_set(v___x_1365_, 0, v___x_1369_);
v___x_1372_ = v___x_1365_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
lean_object* v_k_x27_1374_; uint8_t v___x_1375_; 
v_k_x27_1374_ = lean_array_fget_borrowed(v_ks_1362_, v_x_1359_);
v___x_1375_ = l_Lean_instBEqMVarId_beq(v_x_1360_, v_k_x27_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1377_; 
if (v_isShared_1366_ == 0)
{
v___x_1377_ = v___x_1365_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_ks_1362_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_vs_1363_);
v___x_1377_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_unsigned_to_nat(1u);
v___x_1379_ = lean_nat_add(v_x_1359_, v___x_1378_);
lean_dec(v_x_1359_);
v_x_1358_ = v___x_1377_;
v_x_1359_ = v___x_1379_;
goto _start;
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1382_ = lean_array_fset(v_ks_1362_, v_x_1359_, v_x_1360_);
v___x_1383_ = lean_array_fset(v_vs_1363_, v_x_1359_, v_x_1361_);
lean_dec(v_x_1359_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___x_1383_);
lean_ctor_set(v___x_1365_, 0, v___x_1382_);
v___x_1385_ = v___x_1365_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1388_, lean_object* v_k_1389_, lean_object* v_v_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1388_, v___x_1391_, v_k_1389_, v_v_1390_);
return v___x_1392_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1394_, size_t v_x_1395_, size_t v_x_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_){
_start:
{
if (lean_obj_tag(v_x_1394_) == 0)
{
lean_object* v_es_1399_; size_t v___x_1400_; size_t v___x_1401_; lean_object* v_j_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_es_1399_ = lean_ctor_get(v_x_1394_, 0);
v___x_1400_ = ((size_t)31ULL);
v___x_1401_ = lean_usize_land(v_x_1395_, v___x_1400_);
v_j_1402_ = lean_usize_to_nat(v___x_1401_);
v___x_1403_ = lean_array_get_size(v_es_1399_);
v___x_1404_ = lean_nat_dec_lt(v_j_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_dec(v_j_1402_);
lean_dec(v_x_1398_);
lean_dec(v_x_1397_);
return v_x_1394_;
}
else
{
lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1443_; 
lean_inc_ref(v_es_1399_);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1443_ == 0)
{
lean_object* v_unused_1444_; 
v_unused_1444_ = lean_ctor_get(v_x_1394_, 0);
lean_dec(v_unused_1444_);
v___x_1406_ = v_x_1394_;
v_isShared_1407_ = v_isSharedCheck_1443_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v_x_1394_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1443_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_v_1408_; lean_object* v___x_1409_; lean_object* v_xs_x27_1410_; lean_object* v___y_1412_; 
v_v_1408_ = lean_array_fget(v_es_1399_, v_j_1402_);
v___x_1409_ = lean_box(0);
v_xs_x27_1410_ = lean_array_fset(v_es_1399_, v_j_1402_, v___x_1409_);
switch(lean_obj_tag(v_v_1408_))
{
case 0:
{
lean_object* v_key_1417_; lean_object* v_val_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1428_; 
v_key_1417_ = lean_ctor_get(v_v_1408_, 0);
v_val_1418_ = lean_ctor_get(v_v_1408_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_v_1408_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1420_ = v_v_1408_;
v_isShared_1421_ = v_isSharedCheck_1428_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_val_1418_);
lean_inc(v_key_1417_);
lean_dec(v_v_1408_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1428_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
uint8_t v___x_1422_; 
v___x_1422_ = l_Lean_instBEqMVarId_beq(v_x_1397_, v_key_1417_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_del_object(v___x_1420_);
v___x_1423_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1417_, v_val_1418_, v_x_1397_, v_x_1398_);
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
v___y_1412_ = v___x_1424_;
goto v___jp_1411_;
}
else
{
lean_object* v___x_1426_; 
lean_dec(v_val_1418_);
lean_dec(v_key_1417_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v_x_1398_);
lean_ctor_set(v___x_1420_, 0, v_x_1397_);
v___x_1426_ = v___x_1420_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_x_1397_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_x_1398_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
v___y_1412_ = v___x_1426_;
goto v___jp_1411_;
}
}
}
}
case 1:
{
lean_object* v_node_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1441_; 
v_node_1429_ = lean_ctor_get(v_v_1408_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_v_1408_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1431_ = v_v_1408_;
v_isShared_1432_ = v_isSharedCheck_1441_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_node_1429_);
lean_dec(v_v_1408_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1441_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
size_t v___x_1433_; size_t v___x_1434_; size_t v___x_1435_; size_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1433_ = ((size_t)5ULL);
v___x_1434_ = lean_usize_shift_right(v_x_1395_, v___x_1433_);
v___x_1435_ = ((size_t)1ULL);
v___x_1436_ = lean_usize_add(v_x_1396_, v___x_1435_);
v___x_1437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1429_, v___x_1434_, v___x_1436_, v_x_1397_, v_x_1398_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1437_);
v___x_1439_ = v___x_1431_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
v___y_1412_ = v___x_1439_;
goto v___jp_1411_;
}
}
}
default: 
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v_x_1397_);
lean_ctor_set(v___x_1442_, 1, v_x_1398_);
v___y_1412_ = v___x_1442_;
goto v___jp_1411_;
}
}
v___jp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1413_ = lean_array_fset(v_xs_x27_1410_, v_j_1402_, v___y_1412_);
lean_dec(v_j_1402_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1413_);
v___x_1415_ = v___x_1406_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
else
{
lean_object* v_ks_1445_; lean_object* v_vs_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1466_; 
v_ks_1445_ = lean_ctor_get(v_x_1394_, 0);
v_vs_1446_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1448_ = v_x_1394_;
v_isShared_1449_ = v_isSharedCheck_1466_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_vs_1446_);
lean_inc(v_ks_1445_);
lean_dec(v_x_1394_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1466_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_ks_1445_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_vs_1446_);
v___x_1451_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v_newNode_1452_; uint8_t v___y_1454_; size_t v___x_1460_; uint8_t v___x_1461_; 
v_newNode_1452_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1451_, v_x_1397_, v_x_1398_);
v___x_1460_ = ((size_t)7ULL);
v___x_1461_ = lean_usize_dec_le(v___x_1460_, v_x_1396_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1462_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1452_);
v___x_1463_ = lean_unsigned_to_nat(4u);
v___x_1464_ = lean_nat_dec_lt(v___x_1462_, v___x_1463_);
lean_dec(v___x_1462_);
v___y_1454_ = v___x_1464_;
goto v___jp_1453_;
}
else
{
v___y_1454_ = v___x_1461_;
goto v___jp_1453_;
}
v___jp_1453_:
{
if (v___y_1454_ == 0)
{
lean_object* v_ks_1455_; lean_object* v_vs_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_ks_1455_ = lean_ctor_get(v_newNode_1452_, 0);
lean_inc_ref(v_ks_1455_);
v_vs_1456_ = lean_ctor_get(v_newNode_1452_, 1);
lean_inc_ref(v_vs_1456_);
lean_dec_ref(v_newNode_1452_);
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1459_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1396_, v_ks_1455_, v_vs_1456_, v___x_1457_, v___x_1458_);
lean_dec_ref(v_vs_1456_);
lean_dec_ref(v_ks_1455_);
return v___x_1459_;
}
else
{
return v_newNode_1452_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1467_, lean_object* v_keys_1468_, lean_object* v_vals_1469_, lean_object* v_i_1470_, lean_object* v_entries_1471_){
_start:
{
lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1472_ = lean_array_get_size(v_keys_1468_);
v___x_1473_ = lean_nat_dec_lt(v_i_1470_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_dec(v_i_1470_);
return v_entries_1471_;
}
else
{
lean_object* v_k_1474_; lean_object* v_v_1475_; uint64_t v___x_1476_; size_t v_h_1477_; size_t v___x_1478_; lean_object* v___x_1479_; size_t v___x_1480_; size_t v___x_1481_; size_t v___x_1482_; size_t v_h_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_k_1474_ = lean_array_fget_borrowed(v_keys_1468_, v_i_1470_);
v_v_1475_ = lean_array_fget_borrowed(v_vals_1469_, v_i_1470_);
v___x_1476_ = l_Lean_instHashableMVarId_hash(v_k_1474_);
v_h_1477_ = lean_uint64_to_usize(v___x_1476_);
v___x_1478_ = ((size_t)5ULL);
v___x_1479_ = lean_unsigned_to_nat(1u);
v___x_1480_ = ((size_t)1ULL);
v___x_1481_ = lean_usize_sub(v_depth_1467_, v___x_1480_);
v___x_1482_ = lean_usize_mul(v___x_1478_, v___x_1481_);
v_h_1483_ = lean_usize_shift_right(v_h_1477_, v___x_1482_);
v___x_1484_ = lean_nat_add(v_i_1470_, v___x_1479_);
lean_dec(v_i_1470_);
lean_inc(v_v_1475_);
lean_inc(v_k_1474_);
v___x_1485_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1471_, v_h_1483_, v_depth_1467_, v_k_1474_, v_v_1475_);
v_i_1470_ = v___x_1484_;
v_entries_1471_ = v___x_1485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1487_, lean_object* v_keys_1488_, lean_object* v_vals_1489_, lean_object* v_i_1490_, lean_object* v_entries_1491_){
_start:
{
size_t v_depth_boxed_1492_; lean_object* v_res_1493_; 
v_depth_boxed_1492_ = lean_unbox_usize(v_depth_1487_);
lean_dec(v_depth_1487_);
v_res_1493_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1492_, v_keys_1488_, v_vals_1489_, v_i_1490_, v_entries_1491_);
lean_dec_ref(v_vals_1489_);
lean_dec_ref(v_keys_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_){
_start:
{
size_t v_x_824__boxed_1499_; size_t v_x_825__boxed_1500_; lean_object* v_res_1501_; 
v_x_824__boxed_1499_ = lean_unbox_usize(v_x_1495_);
lean_dec(v_x_1495_);
v_x_825__boxed_1500_ = lean_unbox_usize(v_x_1496_);
lean_dec(v_x_1496_);
v_res_1501_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1494_, v_x_824__boxed_1499_, v_x_825__boxed_1500_, v_x_1497_, v_x_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_){
_start:
{
uint64_t v___x_1505_; size_t v___x_1506_; size_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1505_ = l_Lean_instHashableMVarId_hash(v_x_1503_);
v___x_1506_ = lean_uint64_to_usize(v___x_1505_);
v___x_1507_ = ((size_t)1ULL);
v___x_1508_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1502_, v___x_1506_, v___x_1507_, v_x_1503_, v_x_1504_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1509_, lean_object* v_val_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v_mctx_1514_; lean_object* v_cache_1515_; lean_object* v_zetaDeltaFVarIds_1516_; lean_object* v_postponed_1517_; lean_object* v_diag_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1546_; 
v___x_1513_ = lean_st_ref_take(v___y_1511_);
v_mctx_1514_ = lean_ctor_get(v___x_1513_, 0);
v_cache_1515_ = lean_ctor_get(v___x_1513_, 1);
v_zetaDeltaFVarIds_1516_ = lean_ctor_get(v___x_1513_, 2);
v_postponed_1517_ = lean_ctor_get(v___x_1513_, 3);
v_diag_1518_ = lean_ctor_get(v___x_1513_, 4);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1520_ = v___x_1513_;
v_isShared_1521_ = v_isSharedCheck_1546_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_diag_1518_);
lean_inc(v_postponed_1517_);
lean_inc(v_zetaDeltaFVarIds_1516_);
lean_inc(v_cache_1515_);
lean_inc(v_mctx_1514_);
lean_dec(v___x_1513_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1546_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v_depth_1522_; lean_object* v_levelAssignDepth_1523_; lean_object* v_lmvarCounter_1524_; lean_object* v_mvarCounter_1525_; lean_object* v_lDecls_1526_; lean_object* v_decls_1527_; lean_object* v_userNames_1528_; lean_object* v_lAssignment_1529_; lean_object* v_eAssignment_1530_; lean_object* v_dAssignment_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1545_; 
v_depth_1522_ = lean_ctor_get(v_mctx_1514_, 0);
v_levelAssignDepth_1523_ = lean_ctor_get(v_mctx_1514_, 1);
v_lmvarCounter_1524_ = lean_ctor_get(v_mctx_1514_, 2);
v_mvarCounter_1525_ = lean_ctor_get(v_mctx_1514_, 3);
v_lDecls_1526_ = lean_ctor_get(v_mctx_1514_, 4);
v_decls_1527_ = lean_ctor_get(v_mctx_1514_, 5);
v_userNames_1528_ = lean_ctor_get(v_mctx_1514_, 6);
v_lAssignment_1529_ = lean_ctor_get(v_mctx_1514_, 7);
v_eAssignment_1530_ = lean_ctor_get(v_mctx_1514_, 8);
v_dAssignment_1531_ = lean_ctor_get(v_mctx_1514_, 9);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_mctx_1514_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1533_ = v_mctx_1514_;
v_isShared_1534_ = v_isSharedCheck_1545_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_dAssignment_1531_);
lean_inc(v_eAssignment_1530_);
lean_inc(v_lAssignment_1529_);
lean_inc(v_userNames_1528_);
lean_inc(v_decls_1527_);
lean_inc(v_lDecls_1526_);
lean_inc(v_mvarCounter_1525_);
lean_inc(v_lmvarCounter_1524_);
lean_inc(v_levelAssignDepth_1523_);
lean_inc(v_depth_1522_);
lean_dec(v_mctx_1514_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1545_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1535_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1530_, v_mvarId_1509_, v_val_1510_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 8, v___x_1535_);
v___x_1537_ = v___x_1533_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_depth_1522_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_levelAssignDepth_1523_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_lmvarCounter_1524_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v_mvarCounter_1525_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v_lDecls_1526_);
lean_ctor_set(v_reuseFailAlloc_1544_, 5, v_decls_1527_);
lean_ctor_set(v_reuseFailAlloc_1544_, 6, v_userNames_1528_);
lean_ctor_set(v_reuseFailAlloc_1544_, 7, v_lAssignment_1529_);
lean_ctor_set(v_reuseFailAlloc_1544_, 8, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1544_, 9, v_dAssignment_1531_);
v___x_1537_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1539_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1537_);
v___x_1539_ = v___x_1520_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_cache_1515_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_zetaDeltaFVarIds_1516_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_postponed_1517_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v_diag_1518_);
v___x_1539_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = lean_st_ref_set(v___y_1511_, v___x_1539_);
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1547_, lean_object* v_val_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1547_, v_val_1548_, v___y_1549_);
lean_dec(v___y_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; 
lean_inc(v_g_1552_);
v___x_1558_ = l_Lean_MVarId_getType(v_g_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1560_ = lean_box(0);
v___x_1561_ = l_Lean_Meta_synthInstance(v_a_1559_, v___x_1560_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1571_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v___x_1563_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1552_, v_a_1562_, v___y_1554_);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v___x_1563_, 0);
lean_dec(v_unused_1572_);
v___x_1565_ = v___x_1563_;
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
else
{
lean_dec(v___x_1563_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = lean_box(0);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1567_);
v___x_1569_ = v___x_1565_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v_g_1552_);
v_a_1573_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1561_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1561_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_g_1552_);
v_a_1581_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1558_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1558_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1597_){
_start:
{
lean_object* v___f_1598_; lean_object* v___x_1599_; 
v___f_1598_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1599_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1597_, v___f_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1600_, lean_object* v_val_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1600_, v_val_1601_, v___y_1603_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1608_, lean_object* v_val_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1608_, v_val_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1617_, v_x_1618_, v_x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1621_, lean_object* v_x_1622_, size_t v_x_1623_, size_t v_x_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1622_, v_x_1623_, v_x_1624_, v_x_1625_, v_x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
size_t v_x_1149__boxed_1634_; size_t v_x_1150__boxed_1635_; lean_object* v_res_1636_; 
v_x_1149__boxed_1634_ = lean_unbox_usize(v_x_1630_);
lean_dec(v_x_1630_);
v_x_1150__boxed_1635_ = lean_unbox_usize(v_x_1631_);
lean_dec(v_x_1631_);
v_res_1636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1628_, v_x_1629_, v_x_1149__boxed_1634_, v_x_1150__boxed_1635_, v_x_1632_, v_x_1633_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1637_, lean_object* v_n_1638_, lean_object* v_k_1639_, lean_object* v_v_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1638_, v_k_1639_, v_v_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1642_, size_t v_depth_1643_, lean_object* v_keys_1644_, lean_object* v_vals_1645_, lean_object* v_heq_1646_, lean_object* v_i_1647_, lean_object* v_entries_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1643_, v_keys_1644_, v_vals_1645_, v_i_1647_, v_entries_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1650_, lean_object* v_depth_1651_, lean_object* v_keys_1652_, lean_object* v_vals_1653_, lean_object* v_heq_1654_, lean_object* v_i_1655_, lean_object* v_entries_1656_){
_start:
{
size_t v_depth_boxed_1657_; lean_object* v_res_1658_; 
v_depth_boxed_1657_ = lean_unbox_usize(v_depth_1651_);
lean_dec(v_depth_1651_);
v_res_1658_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1650_, v_depth_boxed_1657_, v_keys_1652_, v_vals_1653_, v_heq_1654_, v_i_1655_, v_entries_1656_);
lean_dec_ref(v_vals_1653_);
lean_dec_ref(v_keys_1652_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1659_, lean_object* v_x_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1660_, v_x_1661_, v_x_1662_, v_x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1665_, lean_object* v_discharge_1666_, lean_object* v_g_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; 
lean_inc(v___y_1671_);
lean_inc_ref(v___y_1670_);
lean_inc(v___y_1669_);
lean_inc_ref(v___y_1668_);
lean_inc(v_g_1667_);
v___x_1673_ = lean_apply_6(v_discharge_1665_, v_g_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, lean_box(0));
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_dec(v_g_1667_);
lean_dec_ref(v_discharge_1666_);
return v___x_1673_;
}
else
{
lean_object* v_a_1674_; uint8_t v___y_1676_; uint8_t v___x_1678_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
v___x_1678_ = l_Lean_Exception_isInterrupt(v_a_1674_);
if (v___x_1678_ == 0)
{
uint8_t v___x_1679_; 
v___x_1679_ = l_Lean_Exception_isRuntime(v_a_1674_);
v___y_1676_ = v___x_1679_;
goto v___jp_1675_;
}
else
{
lean_dec(v_a_1674_);
v___y_1676_ = v___x_1678_;
goto v___jp_1675_;
}
v___jp_1675_:
{
if (v___y_1676_ == 0)
{
lean_object* v___x_1677_; 
lean_dec_ref_known(v___x_1673_, 1);
lean_inc(v___y_1671_);
lean_inc_ref(v___y_1670_);
lean_inc(v___y_1669_);
lean_inc_ref(v___y_1668_);
v___x_1677_ = lean_apply_6(v_discharge_1666_, v_g_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, lean_box(0));
return v___x_1677_;
}
else
{
lean_dec(v_g_1667_);
lean_dec_ref(v_discharge_1666_);
return v___x_1673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1680_, lean_object* v_discharge_1681_, lean_object* v_g_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1680_, v_discharge_1681_, v_g_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1689_, lean_object* v_discharge_1690_){
_start:
{
lean_object* v_toApplyRulesConfig_1691_; lean_object* v_toBacktrackConfig_1692_; uint8_t v_backtracking_1693_; uint8_t v_intro_1694_; uint8_t v_constructor_1695_; uint8_t v_suggestions_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1728_; 
v_toApplyRulesConfig_1691_ = lean_ctor_get(v_cfg_1689_, 0);
lean_inc_ref(v_toApplyRulesConfig_1691_);
v_toBacktrackConfig_1692_ = lean_ctor_get(v_toApplyRulesConfig_1691_, 0);
lean_inc_ref(v_toBacktrackConfig_1692_);
v_backtracking_1693_ = lean_ctor_get_uint8(v_cfg_1689_, sizeof(void*)*1);
v_intro_1694_ = lean_ctor_get_uint8(v_cfg_1689_, sizeof(void*)*1 + 1);
v_constructor_1695_ = lean_ctor_get_uint8(v_cfg_1689_, sizeof(void*)*1 + 2);
v_suggestions_1696_ = lean_ctor_get_uint8(v_cfg_1689_, sizeof(void*)*1 + 3);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_cfg_1689_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v_cfg_1689_, 0);
lean_dec(v_unused_1729_);
v___x_1698_ = v_cfg_1689_;
v_isShared_1699_ = v_isSharedCheck_1728_;
goto v_resetjp_1697_;
}
else
{
lean_dec(v_cfg_1689_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1728_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v_toApplyConfig_1700_; uint8_t v_transparency_1701_; uint8_t v_symm_1702_; uint8_t v_exfalso_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1726_; 
v_toApplyConfig_1700_ = lean_ctor_get(v_toApplyRulesConfig_1691_, 1);
v_transparency_1701_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1691_, sizeof(void*)*2);
v_symm_1702_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1691_, sizeof(void*)*2 + 1);
v_exfalso_1703_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1691_, sizeof(void*)*2 + 2);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_toApplyRulesConfig_1691_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v_toApplyRulesConfig_1691_, 0);
lean_dec(v_unused_1727_);
v___x_1705_ = v_toApplyRulesConfig_1691_;
v_isShared_1706_ = v_isSharedCheck_1726_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_toApplyConfig_1700_);
lean_dec(v_toApplyRulesConfig_1691_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1726_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v_maxDepth_1707_; lean_object* v_proc_1708_; lean_object* v_suspend_1709_; lean_object* v_discharge_1710_; uint8_t v_commitIndependentGoals_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1725_; 
v_maxDepth_1707_ = lean_ctor_get(v_toBacktrackConfig_1692_, 0);
v_proc_1708_ = lean_ctor_get(v_toBacktrackConfig_1692_, 1);
v_suspend_1709_ = lean_ctor_get(v_toBacktrackConfig_1692_, 2);
v_discharge_1710_ = lean_ctor_get(v_toBacktrackConfig_1692_, 3);
v_commitIndependentGoals_1711_ = lean_ctor_get_uint8(v_toBacktrackConfig_1692_, sizeof(void*)*4);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_toBacktrackConfig_1692_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1713_ = v_toBacktrackConfig_1692_;
v_isShared_1714_ = v_isSharedCheck_1725_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_discharge_1710_);
lean_inc(v_suspend_1709_);
lean_inc(v_proc_1708_);
lean_inc(v_maxDepth_1707_);
lean_dec(v_toBacktrackConfig_1692_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1725_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___f_1715_; lean_object* v___x_1717_; 
v___f_1715_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1715_, 0, v_discharge_1690_);
lean_closure_set(v___f_1715_, 1, v_discharge_1710_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 3, v___f_1715_);
v___x_1717_ = v___x_1713_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_maxDepth_1707_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_proc_1708_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_suspend_1709_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v___f_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, sizeof(void*)*4, v_commitIndependentGoals_1711_);
v___x_1717_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1717_);
v___x_1719_ = v___x_1705_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_toApplyConfig_1700_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*2, v_transparency_1701_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*2 + 1, v_symm_1702_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*2 + 2, v_exfalso_1703_);
v___x_1719_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1721_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1719_);
v___x_1721_ = v___x_1698_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*1, v_backtracking_1693_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*1 + 1, v_intro_1694_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*1 + 2, v_constructor_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*1 + 3, v_suggestions_1696_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
uint8_t v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = 1;
v___x_1737_ = l_Lean_Meta_intro1Core(v_g_1730_, v___x_1736_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1756_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1756_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1756_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v_snd_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1754_; 
v_snd_1742_ = lean_ctor_get(v_a_1738_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_a_1738_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v_a_1738_, 0);
lean_dec(v_unused_1755_);
v___x_1744_ = v_a_1738_;
v_isShared_1745_ = v_isSharedCheck_1754_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_snd_1742_);
lean_dec(v_a_1738_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1754_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1746_ = lean_box(0);
if (v_isShared_1745_ == 0)
{
lean_ctor_set_tag(v___x_1744_, 1);
lean_ctor_set(v___x_1744_, 1, v___x_1746_);
lean_ctor_set(v___x_1744_, 0, v_snd_1742_);
v___x_1748_ = v___x_1744_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_snd_1742_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1749_);
v___x_1751_ = v___x_1740_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
v_a_1757_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1737_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1737_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1773_){
_start:
{
lean_object* v___f_1774_; lean_object* v___x_1775_; 
v___f_1774_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1775_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1773_, v___f_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1787_ = l_Lean_MVarId_constructor(v_g_1780_, v___x_1786_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1796_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1796_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1796_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1792_, 0, v_a_1788_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1792_);
v___x_1794_ = v___x_1790_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
v_a_1797_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1787_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1787_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1813_){
_start:
{
lean_object* v___f_1814_; lean_object* v___x_1815_; 
v___f_1814_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1815_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1813_, v___f_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; 
lean_inc(v_g_1818_);
v___x_1824_ = l_Lean_MVarId_getType(v_g_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v___x_1826_ = lean_box(0);
v___x_1827_ = l_Lean_Meta_synthInstance(v_a_1825_, v___x_1826_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1837_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1829_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1818_, v_a_1828_, v___y_1820_);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; 
v_unused_1838_ = lean_ctor_get(v___x_1829_, 0);
lean_dec(v_unused_1838_);
v___x_1831_ = v___x_1829_;
v_isShared_1832_ = v_isSharedCheck_1837_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v___x_1829_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1837_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1833_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v_g_1818_);
v_a_1839_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1827_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1827_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_g_1818_);
v_a_1847_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1824_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1824_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1863_){
_start:
{
lean_object* v___f_1864_; lean_object* v___x_1865_; 
v___f_1864_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1865_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1863_, v___f_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1866_, lean_object* v___y_1867_){
_start:
{
uint8_t v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = l_Lean_Expr_hasMVar(v_e_1866_);
v___x_1870_ = lean_bool_not(v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v_mctx_1872_; lean_object* v___x_1873_; lean_object* v_fst_1874_; lean_object* v_snd_1875_; lean_object* v___x_1876_; lean_object* v_cache_1877_; lean_object* v_zetaDeltaFVarIds_1878_; lean_object* v_postponed_1879_; lean_object* v_diag_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1889_; 
v___x_1871_ = lean_st_ref_get(v___y_1867_);
v_mctx_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc_ref(v_mctx_1872_);
lean_dec(v___x_1871_);
v___x_1873_ = l_Lean_instantiateMVarsCore(v_mctx_1872_, v_e_1866_);
v_fst_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_fst_1874_);
v_snd_1875_ = lean_ctor_get(v___x_1873_, 1);
lean_inc(v_snd_1875_);
lean_dec_ref(v___x_1873_);
v___x_1876_ = lean_st_ref_take(v___y_1867_);
v_cache_1877_ = lean_ctor_get(v___x_1876_, 1);
v_zetaDeltaFVarIds_1878_ = lean_ctor_get(v___x_1876_, 2);
v_postponed_1879_ = lean_ctor_get(v___x_1876_, 3);
v_diag_1880_ = lean_ctor_get(v___x_1876_, 4);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v___x_1876_, 0);
lean_dec(v_unused_1890_);
v___x_1882_ = v___x_1876_;
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_diag_1880_);
lean_inc(v_postponed_1879_);
lean_inc(v_zetaDeltaFVarIds_1878_);
lean_inc(v_cache_1877_);
lean_dec(v___x_1876_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v_snd_1875_);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_snd_1875_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_cache_1877_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_zetaDeltaFVarIds_1878_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_postponed_1879_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v_diag_1880_);
v___x_1885_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_st_ref_set(v___y_1867_, v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_fst_1874_);
return v___x_1887_;
}
}
}
else
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v_e_1866_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1892_, v___y_1893_);
lean_dec(v___y_1893_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1896_, v___y_1898_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1910_, lean_object* v_x_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1910_, v_x_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
v_a_1926_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1917_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1917_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1934_, lean_object* v_x_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1934_, v_x_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1942_, lean_object* v_mvarId_1943_, lean_object* v_x_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1943_, v_x_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1951_, lean_object* v_mvarId_1952_, lean_object* v_x_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1951_, v_mvarId_1952_, v_x_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_ref_1966_; lean_object* v___x_1967_; lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1976_; 
v_ref_1966_ = lean_ctor_get(v___y_1963_, 5);
v___x_1967_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1974_; 
lean_inc(v_ref_1966_);
v___x_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1972_, 0, v_ref_1966_);
lean_ctor_set(v___x_1972_, 1, v_a_1968_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set_tag(v___x_1970_, 1);
lean_ctor_set(v___x_1970_, 0, v___x_1972_);
v___x_1974_ = v___x_1970_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1984_, lean_object* v_x_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
if (lean_obj_tag(v_x_1984_) == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = l_List_reverse___redArg(v_x_1985_);
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
return v___x_1992_;
}
else
{
lean_object* v_head_1993_; lean_object* v_tail_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2014_; 
v_head_1993_ = lean_ctor_get(v_x_1984_, 0);
v_tail_1994_ = lean_ctor_get(v_x_1984_, 1);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_x_1984_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1996_ = v_x_1984_;
v_isShared_1997_ = v_isSharedCheck_2014_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_tail_1994_);
lean_inc(v_head_1993_);
lean_dec(v_x_1984_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2014_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_inc(v_head_1993_);
v___x_1998_ = l_Lean_Expr_mvar___override(v_head_1993_);
v___x_1999_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1999_, 0, v___x_1998_);
v___x_2000_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1993_, v___x_1999_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v_x_1985_);
lean_ctor_set(v___x_1996_, 0, v_a_2001_);
v___x_2003_ = v___x_1996_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_2001_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_x_1985_);
v___x_2003_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
v_x_1984_ = v_tail_1994_;
v_x_1985_ = v___x_2003_;
goto _start;
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_del_object(v___x_1996_);
lean_dec(v_tail_1994_);
lean_dec(v_x_1985_);
v_a_2006_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_2000_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2000_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_2015_, lean_object* v_x_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_2015_, v_x_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
return v_res_2022_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_2025_ = l_Lean_stringToMessageData(v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_2026_, lean_object* v_proc_2027_, lean_object* v_orig_2028_, lean_object* v_goals_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = lean_box(0);
lean_inc(v_orig_2028_);
v___x_2036_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_2028_, v___x_2035_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2032_);
lean_inc(v___y_2031_);
lean_inc_ref(v___y_2030_);
v___x_2038_ = lean_apply_6(v_test_2026_, v_a_2037_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, lean_box(0));
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; uint8_t v___x_2040_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2040_ = lean_unbox(v_a_2039_);
lean_dec(v_a_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_goals_2029_);
lean_dec(v_orig_2028_);
lean_dec_ref(v_proc_2027_);
v___x_2041_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_2042_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2041_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
lean_object* v___x_2051_; 
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2032_);
lean_inc(v___y_2031_);
lean_inc_ref(v___y_2030_);
v___x_2051_ = lean_apply_7(v_proc_2027_, v_orig_2028_, v_goals_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, lean_box(0));
return v___x_2051_;
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v_goals_2029_);
lean_dec(v_orig_2028_);
lean_dec_ref(v_proc_2027_);
v_a_2052_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2038_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2038_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_goals_2029_);
lean_dec(v_orig_2028_);
lean_dec_ref(v_proc_2027_);
lean_dec_ref(v_test_2026_);
v_a_2060_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2036_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2036_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_2068_, lean_object* v_proc_2069_, lean_object* v_orig_2070_, lean_object* v_goals_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_2068_, v_proc_2069_, v_orig_2070_, v_goals_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_2078_, lean_object* v_test_2079_){
_start:
{
lean_object* v_toApplyRulesConfig_2080_; lean_object* v_toBacktrackConfig_2081_; uint8_t v_backtracking_2082_; uint8_t v_intro_2083_; uint8_t v_constructor_2084_; uint8_t v_suggestions_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2117_; 
v_toApplyRulesConfig_2080_ = lean_ctor_get(v_cfg_2078_, 0);
lean_inc_ref(v_toApplyRulesConfig_2080_);
v_toBacktrackConfig_2081_ = lean_ctor_get(v_toApplyRulesConfig_2080_, 0);
lean_inc_ref(v_toBacktrackConfig_2081_);
v_backtracking_2082_ = lean_ctor_get_uint8(v_cfg_2078_, sizeof(void*)*1);
v_intro_2083_ = lean_ctor_get_uint8(v_cfg_2078_, sizeof(void*)*1 + 1);
v_constructor_2084_ = lean_ctor_get_uint8(v_cfg_2078_, sizeof(void*)*1 + 2);
v_suggestions_2085_ = lean_ctor_get_uint8(v_cfg_2078_, sizeof(void*)*1 + 3);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_cfg_2078_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v_cfg_2078_, 0);
lean_dec(v_unused_2118_);
v___x_2087_ = v_cfg_2078_;
v_isShared_2088_ = v_isSharedCheck_2117_;
goto v_resetjp_2086_;
}
else
{
lean_dec(v_cfg_2078_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2117_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v_toApplyConfig_2089_; uint8_t v_transparency_2090_; uint8_t v_symm_2091_; uint8_t v_exfalso_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2115_; 
v_toApplyConfig_2089_ = lean_ctor_get(v_toApplyRulesConfig_2080_, 1);
v_transparency_2090_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2080_, sizeof(void*)*2);
v_symm_2091_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2080_, sizeof(void*)*2 + 1);
v_exfalso_2092_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2080_, sizeof(void*)*2 + 2);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_toApplyRulesConfig_2080_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v_toApplyRulesConfig_2080_, 0);
lean_dec(v_unused_2116_);
v___x_2094_ = v_toApplyRulesConfig_2080_;
v_isShared_2095_ = v_isSharedCheck_2115_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_toApplyConfig_2089_);
lean_dec(v_toApplyRulesConfig_2080_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2115_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_maxDepth_2096_; lean_object* v_proc_2097_; lean_object* v_suspend_2098_; lean_object* v_discharge_2099_; uint8_t v_commitIndependentGoals_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2114_; 
v_maxDepth_2096_ = lean_ctor_get(v_toBacktrackConfig_2081_, 0);
v_proc_2097_ = lean_ctor_get(v_toBacktrackConfig_2081_, 1);
v_suspend_2098_ = lean_ctor_get(v_toBacktrackConfig_2081_, 2);
v_discharge_2099_ = lean_ctor_get(v_toBacktrackConfig_2081_, 3);
v_commitIndependentGoals_2100_ = lean_ctor_get_uint8(v_toBacktrackConfig_2081_, sizeof(void*)*4);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_toBacktrackConfig_2081_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2102_ = v_toBacktrackConfig_2081_;
v_isShared_2103_ = v_isSharedCheck_2114_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_discharge_2099_);
lean_inc(v_suspend_2098_);
lean_inc(v_proc_2097_);
lean_inc(v_maxDepth_2096_);
lean_dec(v_toBacktrackConfig_2081_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2114_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___f_2104_; lean_object* v___x_2106_; 
v___f_2104_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2104_, 0, v_test_2079_);
lean_closure_set(v___f_2104_, 1, v_proc_2097_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 1, v___f_2104_);
v___x_2106_ = v___x_2102_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_maxDepth_2096_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v___f_2104_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_suspend_2098_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_discharge_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*4, v_commitIndependentGoals_2100_);
v___x_2106_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2106_);
v___x_2108_ = v___x_2094_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_toApplyConfig_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*2, v_transparency_2090_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*2 + 1, v_symm_2091_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*2 + 2, v_exfalso_2092_);
v___x_2108_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2108_);
v___x_2110_ = v___x_2087_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
lean_ctor_set_uint8(v_reuseFailAlloc_2111_, sizeof(void*)*1, v_backtracking_2082_);
lean_ctor_set_uint8(v_reuseFailAlloc_2111_, sizeof(void*)*1 + 1, v_intro_2083_);
lean_ctor_set_uint8(v_reuseFailAlloc_2111_, sizeof(void*)*1 + 2, v_constructor_2084_);
lean_ctor_set_uint8(v_reuseFailAlloc_2111_, sizeof(void*)*1 + 3, v_suggestions_2085_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2119_, lean_object* v_msg_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2127_, lean_object* v_msg_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2127_, v_msg_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
return v_res_2134_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2135_){
_start:
{
if (lean_obj_tag(v_x_2135_) == 0)
{
uint8_t v___x_2136_; 
v___x_2136_ = 0;
return v___x_2136_;
}
else
{
lean_object* v_head_2137_; lean_object* v_tail_2138_; uint8_t v___x_2139_; 
v_head_2137_ = lean_ctor_get(v_x_2135_, 0);
v_tail_2138_ = lean_ctor_get(v_x_2135_, 1);
v___x_2139_ = l_Lean_Expr_hasMVar(v_head_2137_);
if (v___x_2139_ == 0)
{
v_x_2135_ = v_tail_2138_;
goto _start;
}
else
{
return v___x_2139_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2141_){
_start:
{
uint8_t v_res_2142_; lean_object* v_r_2143_; 
v_res_2142_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2141_);
lean_dec(v_x_2141_);
v_r_2143_ = lean_box(v_res_2142_);
return v_r_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2144_, lean_object* v_sols_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
uint8_t v___x_2151_; 
v___x_2151_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2145_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; 
lean_inc(v___y_2149_);
lean_inc_ref(v___y_2148_);
lean_inc(v___y_2147_);
lean_inc_ref(v___y_2146_);
v___x_2152_ = lean_apply_6(v_test_2144_, v_sols_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, lean_box(0));
return v___x_2152_;
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec(v_sols_2145_);
lean_dec_ref(v_test_2144_);
v___x_2153_ = lean_box(v___x_2151_);
v___x_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2155_, lean_object* v_sols_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2155_, v_sols_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2163_, lean_object* v_test_2164_){
_start:
{
lean_object* v___f_2165_; lean_object* v___x_2166_; 
v___f_2165_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2165_, 0, v_test_2164_);
v___x_2166_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2163_, v___f_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2167_, lean_object* v_x_2168_){
_start:
{
if (lean_obj_tag(v_x_2168_) == 0)
{
uint8_t v___x_2169_; 
lean_dec_ref(v_e_2167_);
v___x_2169_ = 0;
return v___x_2169_;
}
else
{
lean_object* v_head_2170_; lean_object* v_tail_2171_; uint8_t v___x_2172_; 
v_head_2170_ = lean_ctor_get(v_x_2168_, 0);
v_tail_2171_ = lean_ctor_get(v_x_2168_, 1);
lean_inc_ref(v_e_2167_);
v___x_2172_ = l_Lean_Expr_occurs(v_e_2167_, v_head_2170_);
if (v___x_2172_ == 0)
{
v_x_2168_ = v_tail_2171_;
goto _start;
}
else
{
lean_dec_ref(v_e_2167_);
return v___x_2172_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2174_, lean_object* v_x_2175_){
_start:
{
uint8_t v_res_2176_; lean_object* v_r_2177_; 
v_res_2176_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2174_, v_x_2175_);
lean_dec(v_x_2175_);
v_r_2177_ = lean_box(v_res_2176_);
return v_r_2177_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2178_, lean_object* v_x_2179_){
_start:
{
if (lean_obj_tag(v_x_2179_) == 0)
{
uint8_t v___x_2180_; 
v___x_2180_ = 1;
return v___x_2180_;
}
else
{
lean_object* v_head_2181_; lean_object* v_tail_2182_; uint8_t v___x_2183_; 
v_head_2181_ = lean_ctor_get(v_x_2179_, 0);
lean_inc(v_head_2181_);
v_tail_2182_ = lean_ctor_get(v_x_2179_, 1);
lean_inc(v_tail_2182_);
lean_dec_ref_known(v_x_2179_, 2);
v___x_2183_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2181_, v_sols_2178_);
if (v___x_2183_ == 0)
{
lean_dec(v_tail_2182_);
return v___x_2183_;
}
else
{
v_x_2179_ = v_tail_2182_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2185_, lean_object* v_x_2186_){
_start:
{
uint8_t v_res_2187_; lean_object* v_r_2188_; 
v_res_2187_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2185_, v_x_2186_);
lean_dec(v_sols_2185_);
v_r_2188_ = lean_box(v_res_2187_);
return v_r_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2189_, lean_object* v_sols_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
uint8_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2190_, v_use_2189_);
v___x_2197_ = lean_box(v___x_2196_);
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2199_, lean_object* v_sols_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2199_, v_sols_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v_sols_2200_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2207_, lean_object* v_use_2208_){
_start:
{
lean_object* v___f_2209_; lean_object* v___x_2210_; 
v___f_2209_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2209_, 0, v_use_2208_);
v___x_2210_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2207_, v___f_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2211_){
_start:
{
lean_object* v___y_2213_; lean_object* v_toApplyRulesConfig_2214_; uint8_t v_backtracking_2215_; uint8_t v_intro_2216_; uint8_t v_constructor_2217_; uint8_t v_suggestions_2218_; uint8_t v_intro_2222_; 
v_intro_2222_ = lean_ctor_get_uint8(v_cfg_2211_, sizeof(void*)*1 + 1);
if (v_intro_2222_ == 0)
{
lean_object* v_toApplyRulesConfig_2223_; uint8_t v_backtracking_2224_; uint8_t v_constructor_2225_; uint8_t v_suggestions_2226_; 
v_toApplyRulesConfig_2223_ = lean_ctor_get(v_cfg_2211_, 0);
lean_inc_ref(v_toApplyRulesConfig_2223_);
v_backtracking_2224_ = lean_ctor_get_uint8(v_cfg_2211_, sizeof(void*)*1);
v_constructor_2225_ = lean_ctor_get_uint8(v_cfg_2211_, sizeof(void*)*1 + 2);
v_suggestions_2226_ = lean_ctor_get_uint8(v_cfg_2211_, sizeof(void*)*1 + 3);
v___y_2213_ = v_cfg_2211_;
v_toApplyRulesConfig_2214_ = v_toApplyRulesConfig_2223_;
v_backtracking_2215_ = v_backtracking_2224_;
v_intro_2216_ = v_intro_2222_;
v_constructor_2217_ = v_constructor_2225_;
v_suggestions_2218_ = v_suggestions_2226_;
goto v___jp_2212_;
}
else
{
lean_object* v_toApplyRulesConfig_2227_; uint8_t v_backtracking_2228_; uint8_t v_constructor_2229_; uint8_t v_suggestions_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2244_; 
v_toApplyRulesConfig_2227_ = lean_ctor_get(v_cfg_2211_, 0);
v_backtracking_2228_ = lean_ctor_get_uint8(v_cfg_2211_, sizeof(void*)*1);
v_constructor_2229_ = lean_ctor_get_uint8(v_cfg_2211_, sizeof(void*)*1 + 2);
v_suggestions_2230_ = lean_ctor_get_uint8(v_cfg_2211_, sizeof(void*)*1 + 3);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_cfg_2211_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2232_ = v_cfg_2211_;
v_isShared_2233_ = v_isSharedCheck_2244_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_toApplyRulesConfig_2227_);
lean_dec(v_cfg_2211_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2244_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
uint8_t v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = 0;
if (v_isShared_2233_ == 0)
{
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_toApplyRulesConfig_2227_);
lean_ctor_set_uint8(v_reuseFailAlloc_2243_, sizeof(void*)*1, v_backtracking_2228_);
lean_ctor_set_uint8(v_reuseFailAlloc_2243_, sizeof(void*)*1 + 2, v_constructor_2229_);
lean_ctor_set_uint8(v_reuseFailAlloc_2243_, sizeof(void*)*1 + 3, v_suggestions_2230_);
v___x_2236_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; lean_object* v_toApplyRulesConfig_2238_; uint8_t v_backtracking_2239_; uint8_t v_intro_2240_; uint8_t v_constructor_2241_; uint8_t v_suggestions_2242_; 
lean_ctor_set_uint8(v___x_2236_, sizeof(void*)*1 + 1, v___x_2234_);
v___x_2237_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2236_);
v_toApplyRulesConfig_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc_ref(v_toApplyRulesConfig_2238_);
v_backtracking_2239_ = lean_ctor_get_uint8(v___x_2237_, sizeof(void*)*1);
v_intro_2240_ = lean_ctor_get_uint8(v___x_2237_, sizeof(void*)*1 + 1);
v_constructor_2241_ = lean_ctor_get_uint8(v___x_2237_, sizeof(void*)*1 + 2);
v_suggestions_2242_ = lean_ctor_get_uint8(v___x_2237_, sizeof(void*)*1 + 3);
v___y_2213_ = v___x_2237_;
v_toApplyRulesConfig_2214_ = v_toApplyRulesConfig_2238_;
v_backtracking_2215_ = v_backtracking_2239_;
v_intro_2216_ = v_intro_2240_;
v_constructor_2217_ = v_constructor_2241_;
v_suggestions_2218_ = v_suggestions_2242_;
goto v___jp_2212_;
}
}
}
v___jp_2212_:
{
if (v_constructor_2217_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2214_);
return v___y_2213_;
}
else
{
uint8_t v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_dec_ref(v___y_2213_);
v___x_2219_ = 0;
v___x_2220_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2220_, 0, v_toApplyRulesConfig_2214_);
lean_ctor_set_uint8(v___x_2220_, sizeof(void*)*1, v_backtracking_2215_);
lean_ctor_set_uint8(v___x_2220_, sizeof(void*)*1 + 1, v_intro_2216_);
lean_ctor_set_uint8(v___x_2220_, sizeof(void*)*1 + 2, v___x_2219_);
lean_ctor_set_uint8(v___x_2220_, sizeof(void*)*1 + 3, v_suggestions_2218_);
v___x_2221_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2220_);
return v___x_2221_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2245_, lean_object* v_x_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
if (lean_obj_tag(v_x_2245_) == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = l_List_reverse___redArg(v_x_2246_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
return v___x_2255_;
}
else
{
lean_object* v_head_2256_; lean_object* v_tail_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2275_; 
v_head_2256_ = lean_ctor_get(v_x_2245_, 0);
v_tail_2257_ = lean_ctor_get(v_x_2245_, 1);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_x_2245_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2259_ = v_x_2245_;
v_isShared_2260_ = v_isSharedCheck_2275_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_tail_2257_);
lean_inc(v_head_2256_);
lean_dec(v_x_2245_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2275_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; 
lean_inc(v___y_2252_);
lean_inc_ref(v___y_2251_);
lean_inc(v___y_2250_);
lean_inc_ref(v___y_2249_);
lean_inc(v___y_2248_);
lean_inc_ref(v___y_2247_);
v___x_2261_ = lean_apply_7(v_head_2256_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, lean_box(0));
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v_x_2246_);
lean_ctor_set(v___x_2259_, 0, v_a_2262_);
v___x_2264_ = v___x_2259_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2262_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_x_2246_);
v___x_2264_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
v_x_2245_ = v_tail_2257_;
v_x_2246_ = v___x_2264_;
goto _start;
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_del_object(v___x_2259_);
lean_dec(v_tail_2257_);
lean_dec(v_x_2246_);
v_a_2267_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2261_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2261_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2276_, lean_object* v_x_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2276_, v_x_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2286_, lean_object* v_cfg_2287_, lean_object* v_lemmas_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2296_; 
lean_inc(v___y_2294_);
lean_inc_ref(v___y_2293_);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2291_);
lean_inc(v___y_2290_);
lean_inc_ref(v___y_2289_);
v___x_2296_ = lean_apply_8(v_ctx_2286_, v_cfg_2287_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, lean_box(0));
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = lean_box(0);
v___x_2299_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2288_, v___x_2298_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2308_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2304_ = l_List_appendTR___redArg(v_a_2297_, v_a_2300_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2304_);
v___x_2306_ = v___x_2302_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
else
{
lean_dec(v_a_2297_);
return v___x_2299_;
}
}
else
{
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v_lemmas_2288_);
return v___x_2296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2309_, lean_object* v_cfg_2310_, lean_object* v_lemmas_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2309_, v_cfg_2310_, v_lemmas_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
return v_res_2319_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2320_){
_start:
{
uint8_t v___x_2321_; 
v___x_2321_ = 0;
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2322_){
_start:
{
uint8_t v_res_2323_; lean_object* v_r_2324_; 
v_res_2323_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2322_);
lean_dec(v_x_2322_);
v_r_2324_ = lean_box(v_res_2323_);
return v_r_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2325_, lean_object* v___x_2326_, lean_object* v___x_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2325_, v___x_2326_, v___x_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2342_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2342_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2342_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v_fst_2338_; lean_object* v___x_2340_; 
v_fst_2338_ = lean_ctor_get(v_a_2334_, 0);
lean_inc(v_fst_2338_);
lean_dec(v_a_2334_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v_fst_2338_);
v___x_2340_ = v___x_2336_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_fst_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
v_a_2343_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2333_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2333_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2351_, lean_object* v___x_2352_, lean_object* v___x_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2351_, v___x_2352_, v___x_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2374_, lean_object* v_g_2375_, lean_object* v_lemmas_2376_, lean_object* v_ctx_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v___f_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___f_2386_; lean_object* v___x_2387_; 
v___f_2383_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2383_, 0, v_ctx_2377_);
lean_closure_set(v___f_2383_, 1, v_cfg_2374_);
lean_closure_set(v___f_2383_, 2, v_lemmas_2376_);
v___x_2384_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2385_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2386_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2386_, 0, v___f_2383_);
lean_closure_set(v___f_2386_, 1, v___x_2384_);
lean_closure_set(v___f_2386_, 2, v___x_2385_);
v___x_2387_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2375_, v___f_2386_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2388_, lean_object* v_g_2389_, lean_object* v_lemmas_2390_, lean_object* v_ctx_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2388_, v_g_2389_, v_lemmas_2390_, v_ctx_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2398_, lean_object* v_lemmas_2399_, lean_object* v_ctx_2400_, lean_object* v_g_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2407_; 
lean_inc(v_g_2401_);
lean_inc_ref(v_cfg_2398_);
v___x_2407_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2398_, v_g_2401_, v_lemmas_2399_, v_ctx_2400_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_toApplyRulesConfig_2408_; lean_object* v_a_2409_; lean_object* v_toApplyConfig_2410_; uint8_t v_transparency_2411_; lean_object* v___x_2412_; 
v_toApplyRulesConfig_2408_ = lean_ctor_get(v_cfg_2398_, 0);
lean_inc_ref(v_toApplyRulesConfig_2408_);
lean_dec_ref(v_cfg_2398_);
v_a_2409_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2407_, 1);
v_toApplyConfig_2410_ = lean_ctor_get(v_toApplyRulesConfig_2408_, 1);
lean_inc_ref(v_toApplyConfig_2410_);
v_transparency_2411_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2408_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2408_);
v___x_2412_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2410_, v_transparency_2411_, v_a_2409_, v_g_2401_, v_a_2403_, v_a_2405_);
return v___x_2412_;
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec(v_g_2401_);
lean_dec_ref(v_cfg_2398_);
v_a_2413_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2407_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2407_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2421_, lean_object* v_lemmas_2422_, lean_object* v_ctx_2423_, lean_object* v_g_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2421_, v_lemmas_2422_, v_ctx_2423_, v_g_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2431_, lean_object* v_lemmas_2432_, lean_object* v_ctx_2433_, lean_object* v_g_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2440_; 
lean_inc(v_g_2434_);
lean_inc_ref(v_cfg_2431_);
v___x_2440_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2431_, v_g_2434_, v_lemmas_2432_, v_ctx_2433_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_toApplyRulesConfig_2441_; lean_object* v_a_2442_; lean_object* v_toApplyConfig_2443_; uint8_t v_transparency_2444_; lean_object* v___x_2445_; 
v_toApplyRulesConfig_2441_ = lean_ctor_get(v_cfg_2431_, 0);
lean_inc_ref(v_toApplyRulesConfig_2441_);
lean_dec_ref(v_cfg_2431_);
v_a_2442_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2442_);
lean_dec_ref_known(v___x_2440_, 1);
v_toApplyConfig_2443_ = lean_ctor_get(v_toApplyRulesConfig_2441_, 1);
lean_inc_ref(v_toApplyConfig_2443_);
v_transparency_2444_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2441_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2441_);
v___x_2445_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2443_, v_transparency_2444_, v_a_2442_, v_g_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_);
return v___x_2445_;
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_g_2434_);
lean_dec_ref(v_cfg_2431_);
v_a_2446_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2440_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2440_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2454_, lean_object* v_lemmas_2455_, lean_object* v_ctx_2456_, lean_object* v_g_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2454_, v_lemmas_2455_, v_ctx_2456_, v_g_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
return v_res_2463_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2464_, lean_object* v_i_2465_, lean_object* v_k_2466_){
_start:
{
lean_object* v___x_2467_; uint8_t v___x_2468_; 
v___x_2467_ = lean_array_get_size(v_keys_2464_);
v___x_2468_ = lean_nat_dec_lt(v_i_2465_, v___x_2467_);
if (v___x_2468_ == 0)
{
lean_dec(v_i_2465_);
return v___x_2468_;
}
else
{
lean_object* v_k_x27_2469_; uint8_t v___x_2470_; 
v_k_x27_2469_ = lean_array_fget_borrowed(v_keys_2464_, v_i_2465_);
v___x_2470_ = l_Lean_instBEqMVarId_beq(v_k_2466_, v_k_x27_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_unsigned_to_nat(1u);
v___x_2472_ = lean_nat_add(v_i_2465_, v___x_2471_);
lean_dec(v_i_2465_);
v_i_2465_ = v___x_2472_;
goto _start;
}
else
{
lean_dec(v_i_2465_);
return v___x_2470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2474_, lean_object* v_i_2475_, lean_object* v_k_2476_){
_start:
{
uint8_t v_res_2477_; lean_object* v_r_2478_; 
v_res_2477_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2474_, v_i_2475_, v_k_2476_);
lean_dec(v_k_2476_);
lean_dec_ref(v_keys_2474_);
v_r_2478_ = lean_box(v_res_2477_);
return v_r_2478_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2479_, size_t v_x_2480_, lean_object* v_x_2481_){
_start:
{
if (lean_obj_tag(v_x_2479_) == 0)
{
lean_object* v_es_2482_; lean_object* v___x_2483_; size_t v___x_2484_; size_t v___x_2485_; lean_object* v_j_2486_; lean_object* v___x_2487_; 
v_es_2482_ = lean_ctor_get(v_x_2479_, 0);
v___x_2483_ = lean_box(2);
v___x_2484_ = ((size_t)31ULL);
v___x_2485_ = lean_usize_land(v_x_2480_, v___x_2484_);
v_j_2486_ = lean_usize_to_nat(v___x_2485_);
v___x_2487_ = lean_array_get_borrowed(v___x_2483_, v_es_2482_, v_j_2486_);
lean_dec(v_j_2486_);
switch(lean_obj_tag(v___x_2487_))
{
case 0:
{
lean_object* v_key_2488_; uint8_t v___x_2489_; 
v_key_2488_ = lean_ctor_get(v___x_2487_, 0);
v___x_2489_ = l_Lean_instBEqMVarId_beq(v_x_2481_, v_key_2488_);
return v___x_2489_;
}
case 1:
{
lean_object* v_node_2490_; size_t v___x_2491_; size_t v___x_2492_; 
v_node_2490_ = lean_ctor_get(v___x_2487_, 0);
v___x_2491_ = ((size_t)5ULL);
v___x_2492_ = lean_usize_shift_right(v_x_2480_, v___x_2491_);
v_x_2479_ = v_node_2490_;
v_x_2480_ = v___x_2492_;
goto _start;
}
default: 
{
uint8_t v___x_2494_; 
v___x_2494_ = 0;
return v___x_2494_;
}
}
}
else
{
lean_object* v_ks_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v_ks_2495_ = lean_ctor_get(v_x_2479_, 0);
v___x_2496_ = lean_unsigned_to_nat(0u);
v___x_2497_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2495_, v___x_2496_, v_x_2481_);
return v___x_2497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2498_, lean_object* v_x_2499_, lean_object* v_x_2500_){
_start:
{
size_t v_x_2183__boxed_2501_; uint8_t v_res_2502_; lean_object* v_r_2503_; 
v_x_2183__boxed_2501_ = lean_unbox_usize(v_x_2499_);
lean_dec(v_x_2499_);
v_res_2502_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2498_, v_x_2183__boxed_2501_, v_x_2500_);
lean_dec(v_x_2500_);
lean_dec_ref(v_x_2498_);
v_r_2503_ = lean_box(v_res_2502_);
return v_r_2503_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2504_, lean_object* v_x_2505_){
_start:
{
uint64_t v___x_2506_; size_t v___x_2507_; uint8_t v___x_2508_; 
v___x_2506_ = l_Lean_instHashableMVarId_hash(v_x_2505_);
v___x_2507_ = lean_uint64_to_usize(v___x_2506_);
v___x_2508_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2504_, v___x_2507_, v_x_2505_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2509_, lean_object* v_x_2510_){
_start:
{
uint8_t v_res_2511_; lean_object* v_r_2512_; 
v_res_2511_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2509_, v_x_2510_);
lean_dec(v_x_2510_);
lean_dec_ref(v_x_2509_);
v_r_2512_ = lean_box(v_res_2511_);
return v_r_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___x_2516_; lean_object* v_mctx_2517_; lean_object* v_eAssignment_2518_; uint8_t v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2516_ = lean_st_ref_get(v___y_2514_);
v_mctx_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc_ref(v_mctx_2517_);
lean_dec(v___x_2516_);
v_eAssignment_2518_ = lean_ctor_get(v_mctx_2517_, 8);
lean_inc_ref(v_eAssignment_2518_);
lean_dec_ref(v_mctx_2517_);
v___x_2519_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2518_, v_mvarId_2513_);
lean_dec_ref(v_eAssignment_2518_);
v___x_2520_ = lean_box(v___x_2519_);
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec(v_mvarId_2522_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2526_, lean_object* v_x_2527_){
_start:
{
if (lean_obj_tag(v_x_2527_) == 0)
{
return v_x_2526_;
}
else
{
lean_object* v_head_2528_; lean_object* v_tail_2529_; lean_object* v___x_2530_; 
v_head_2528_ = lean_ctor_get(v_x_2527_, 0);
lean_inc(v_head_2528_);
v_tail_2529_ = lean_ctor_get(v_x_2527_, 1);
lean_inc(v_tail_2529_);
lean_dec_ref_known(v_x_2527_, 2);
v___x_2530_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2526_, v_head_2528_);
v_x_2526_ = v___x_2530_;
v_x_2527_ = v_tail_2529_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2532_, lean_object* v_a_2533_, uint8_t v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
if (lean_obj_tag(v_a_2535_) == 0)
{
if (lean_obj_tag(v_a_2536_) == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
lean_dec(v_a_2533_);
lean_dec_ref(v_f_2532_);
v___x_2543_ = lean_box(v_a_2534_);
v___x_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
lean_ctor_set(v___x_2544_, 1, v_a_2537_);
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
return v___x_2545_;
}
else
{
lean_object* v_head_2546_; lean_object* v_tail_2547_; 
v_head_2546_ = lean_ctor_get(v_a_2536_, 0);
lean_inc(v_head_2546_);
v_tail_2547_ = lean_ctor_get(v_a_2536_, 1);
lean_inc(v_tail_2547_);
lean_dec_ref_known(v_a_2536_, 2);
v_a_2535_ = v_head_2546_;
v_a_2536_ = v_tail_2547_;
goto _start;
}
}
else
{
lean_object* v_head_2549_; lean_object* v_tail_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2593_; 
v_head_2549_ = lean_ctor_get(v_a_2535_, 0);
v_tail_2550_ = lean_ctor_get(v_a_2535_, 1);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_a_2535_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2552_ = v_a_2535_;
v_isShared_2553_ = v_isSharedCheck_2593_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_tail_2550_);
lean_inc(v_head_2549_);
lean_dec(v_a_2535_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2593_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2592_; 
v___x_2554_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2549_, v___y_2539_);
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2592_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2592_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
uint8_t v___x_2559_; 
v___x_2559_ = lean_unbox(v_a_2555_);
lean_dec(v_a_2555_);
if (v___x_2559_ == 0)
{
lean_object* v_zero_2560_; uint8_t v_isZero_2561_; 
v_zero_2560_ = lean_unsigned_to_nat(0u);
v_isZero_2561_ = lean_nat_dec_eq(v_a_2533_, v_zero_2560_);
if (v_isZero_2561_ == 1)
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
lean_del_object(v___x_2552_);
lean_dec(v_a_2533_);
lean_dec_ref(v_f_2532_);
v___x_2562_ = lean_array_push(v_a_2537_, v_head_2549_);
v___x_2563_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2562_, v_tail_2550_);
v___x_2564_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2563_, v_a_2536_);
v___x_2565_ = lean_box(v_a_2534_);
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v___x_2564_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2566_);
v___x_2568_ = v___x_2557_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
else
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_del_object(v___x_2557_);
lean_inc_ref(v_f_2532_);
lean_inc(v_head_2549_);
v___x_2570_ = lean_apply_1(v_f_2532_, v_head_2549_);
v___x_2571_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2570_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v_one_2573_; lean_object* v_n_2574_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
v_one_2573_ = lean_unsigned_to_nat(1u);
v_n_2574_ = lean_nat_sub(v_a_2533_, v_one_2573_);
lean_dec(v_a_2533_);
if (lean_obj_tag(v_a_2572_) == 0)
{
lean_object* v___x_2575_; 
lean_del_object(v___x_2552_);
v___x_2575_ = lean_array_push(v_a_2537_, v_head_2549_);
v_a_2533_ = v_n_2574_;
v_a_2535_ = v_tail_2550_;
v_a_2537_ = v___x_2575_;
goto _start;
}
else
{
lean_object* v_val_2577_; uint8_t v___x_2578_; lean_object* v___x_2580_; 
lean_dec(v_head_2549_);
v_val_2577_ = lean_ctor_get(v_a_2572_, 0);
lean_inc(v_val_2577_);
lean_dec_ref_known(v_a_2572_, 1);
v___x_2578_ = 1;
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v_a_2536_);
lean_ctor_set(v___x_2552_, 0, v_tail_2550_);
v___x_2580_ = v___x_2552_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_tail_2550_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_a_2536_);
v___x_2580_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
v_a_2533_ = v_n_2574_;
v_a_2534_ = v___x_2578_;
v_a_2535_ = v_val_2577_;
v_a_2536_ = v___x_2580_;
goto _start;
}
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_del_object(v___x_2552_);
lean_dec(v_tail_2550_);
lean_dec(v_head_2549_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec(v_a_2533_);
lean_dec_ref(v_f_2532_);
v_a_2583_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2571_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2571_);
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
else
{
lean_del_object(v___x_2557_);
lean_del_object(v___x_2552_);
lean_dec(v_head_2549_);
v_a_2535_ = v_tail_2550_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
uint8_t v_a_2262__boxed_2605_; lean_object* v_res_2606_; 
v_a_2262__boxed_2605_ = lean_unbox(v_a_2596_);
v_res_2606_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2594_, v_a_2595_, v_a_2262__boxed_2605_, v_a_2597_, v_a_2598_, v_a_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2607_, size_t v_i_2608_, size_t v_stop_2609_, lean_object* v_b_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_a_2617_; uint8_t v___x_2621_; 
v___x_2621_ = lean_usize_dec_eq(v_i_2608_, v_stop_2609_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; uint8_t v_a_2624_; lean_object* v___x_2626_; 
v___x_2622_ = lean_array_uget_borrowed(v_as_2607_, v_i_2608_);
v___x_2626_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2622_, v___y_2612_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; uint8_t v___x_2628_; uint8_t v___x_2629_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2628_ = lean_unbox(v_a_2627_);
lean_dec(v_a_2627_);
v___x_2629_ = lean_bool_not(v___x_2628_);
v_a_2624_ = v___x_2629_;
goto v___jp_2623_;
}
else
{
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2630_; uint8_t v___x_2631_; 
v_a_2630_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2631_ = lean_unbox(v_a_2630_);
lean_dec(v_a_2630_);
v_a_2624_ = v___x_2631_;
goto v___jp_2623_;
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec_ref(v_b_2610_);
v_a_2632_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2626_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2626_);
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
v___jp_2623_:
{
if (v_a_2624_ == 0)
{
v_a_2617_ = v_b_2610_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2625_; 
lean_inc(v___x_2622_);
v___x_2625_ = lean_array_push(v_b_2610_, v___x_2622_);
v_a_2617_ = v___x_2625_;
goto v___jp_2616_;
}
}
}
else
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v_b_2610_);
return v___x_2640_;
}
v___jp_2616_:
{
size_t v___x_2618_; size_t v___x_2619_; 
v___x_2618_ = ((size_t)1ULL);
v___x_2619_ = lean_usize_add(v_i_2608_, v___x_2618_);
v_i_2608_ = v___x_2619_;
v_b_2610_ = v_a_2617_;
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
lean_dec_ref_known(v___x_2696_, 1);
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
lean_dec_ref_known(v___x_2708_, 1);
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
size_t v_x_2726__boxed_2841_; uint8_t v_res_2842_; lean_object* v_r_2843_; 
v_x_2726__boxed_2841_ = lean_unbox_usize(v_x_2839_);
lean_dec(v_x_2839_);
v_res_2842_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2837_, v_x_2838_, v_x_2726__boxed_2841_, v_x_2840_);
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
v___x_2879_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2));
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
lean_object* v_a_2892_; lean_object* v___f_2893_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; uint8_t v___y_2898_; uint8_t v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v_a_2902_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; uint8_t v___y_2915_; lean_object* v___y_2916_; uint8_t v___y_2917_; lean_object* v___y_2918_; lean_object* v_a_2919_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; uint8_t v___y_2925_; uint8_t v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v_a_2929_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; uint8_t v___y_2945_; lean_object* v___y_2946_; uint8_t v___y_2947_; lean_object* v___y_2948_; lean_object* v_a_2949_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; uint8_t v___y_2956_; uint8_t v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; uint8_t v___y_2998_; lean_object* v___y_2999_; uint8_t v_a_3000_; uint8_t v___y_3016_; uint8_t v___x_3048_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
v___f_2893_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_3048_ = l_Lean_Exception_isInterrupt(v_a_2892_);
if (v___x_3048_ == 0)
{
uint8_t v___x_3049_; 
v___x_3049_ = l_Lean_Exception_isRuntime(v_a_2892_);
v___y_3016_ = v___x_3049_;
goto v___jp_3015_;
}
else
{
lean_dec(v_a_2892_);
v___y_3016_ = v___x_3048_;
goto v___jp_3015_;
}
v___jp_2894_:
{
lean_object* v___x_2903_; double v___x_2904_; double v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2903_ = lean_io_get_num_heartbeats();
v___x_2904_ = lean_float_of_nat(v___y_2897_);
v___x_2905_ = lean_float_of_nat(v___x_2903_);
v___x_2906_ = lean_box_float(v___x_2904_);
v___x_2907_ = lean_box_float(v___x_2905_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v_a_2902_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
lean_inc_ref(v___y_2895_);
lean_inc(v___y_2896_);
v___x_2910_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2896_, v___y_2898_, v___y_2895_, v___y_2900_, v___y_2899_, v___y_2901_, v___f_2893_, v___x_2909_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
return v___x_2910_;
}
v___jp_2911_:
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2920_, 0, v_a_2919_);
v___y_2895_ = v___y_2912_;
v___y_2896_ = v___y_2913_;
v___y_2897_ = v___y_2914_;
v___y_2898_ = v___y_2915_;
v___y_2899_ = v___y_2917_;
v___y_2900_ = v___y_2916_;
v___y_2901_ = v___y_2918_;
v_a_2902_ = v___x_2920_;
goto v___jp_2894_;
}
v___jp_2921_:
{
lean_object* v___x_2930_; double v___x_2931_; double v___x_2932_; double v___x_2933_; double v___x_2934_; double v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2930_ = lean_io_mono_nanos_now();
v___x_2931_ = lean_float_of_nat(v___y_2924_);
v___x_2932_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0);
v___x_2933_ = lean_float_div(v___x_2931_, v___x_2932_);
v___x_2934_ = lean_float_of_nat(v___x_2930_);
v___x_2935_ = lean_float_div(v___x_2934_, v___x_2932_);
v___x_2936_ = lean_box_float(v___x_2933_);
v___x_2937_ = lean_box_float(v___x_2935_);
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v_a_2929_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
lean_inc_ref(v___y_2922_);
lean_inc(v___y_2923_);
v___x_2940_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2923_, v___y_2925_, v___y_2922_, v___y_2927_, v___y_2926_, v___y_2928_, v___f_2893_, v___x_2939_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
return v___x_2940_;
}
v___jp_2941_:
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_a_2949_);
v___y_2922_ = v___y_2942_;
v___y_2923_ = v___y_2943_;
v___y_2924_ = v___y_2944_;
v___y_2925_ = v___y_2945_;
v___y_2926_ = v___y_2947_;
v___y_2927_ = v___y_2946_;
v___y_2928_ = v___y_2948_;
v_a_2929_ = v___x_2950_;
goto v___jp_2921_;
}
v___jp_2951_:
{
lean_object* v___x_2959_; lean_object* v_a_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2959_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2888_);
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref(v___x_2959_);
v___x_2961_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2962_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2958_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = lean_io_mono_nanos_now();
v___x_2964_ = l_Lean_MVarId_exfalso(v___y_2954_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
v___x_2966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2966_, 0, v_a_2965_);
lean_ctor_set(v___x_2966_, 1, v___y_2955_);
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
v___y_2922_ = v___y_2952_;
v___y_2923_ = v___y_2953_;
v___y_2924_ = v___x_2963_;
v___y_2925_ = v___y_2956_;
v___y_2926_ = v___y_2957_;
v___y_2927_ = v___y_2958_;
v___y_2928_ = v_a_2960_;
v_a_2929_ = v___x_2973_;
goto v___jp_2921_;
}
}
}
else
{
lean_object* v_a_2976_; 
v_a_2976_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2976_);
lean_dec_ref_known(v___x_2967_, 1);
v___y_2942_ = v___y_2952_;
v___y_2943_ = v___y_2953_;
v___y_2944_ = v___x_2963_;
v___y_2945_ = v___y_2956_;
v___y_2946_ = v___y_2958_;
v___y_2947_ = v___y_2957_;
v___y_2948_ = v_a_2960_;
v_a_2949_ = v_a_2976_;
goto v___jp_2941_;
}
}
else
{
lean_object* v_a_2977_; 
lean_dec(v___y_2955_);
lean_dec_ref(v_cfg_2890_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
v_a_2977_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2977_);
lean_dec_ref_known(v___x_2964_, 1);
v___y_2942_ = v___y_2952_;
v___y_2943_ = v___y_2953_;
v___y_2944_ = v___x_2963_;
v___y_2945_ = v___y_2956_;
v___y_2946_ = v___y_2958_;
v___y_2947_ = v___y_2957_;
v___y_2948_ = v_a_2960_;
v_a_2949_ = v_a_2977_;
goto v___jp_2941_;
}
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_io_get_num_heartbeats();
v___x_2979_ = l_Lean_MVarId_exfalso(v___y_2954_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2981_, 0, v_a_2980_);
lean_ctor_set(v___x_2981_, 1, v___y_2955_);
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
v___y_2895_ = v___y_2952_;
v___y_2896_ = v___y_2953_;
v___y_2897_ = v___x_2978_;
v___y_2898_ = v___y_2956_;
v___y_2899_ = v___y_2957_;
v___y_2900_ = v___y_2958_;
v___y_2901_ = v_a_2960_;
v_a_2902_ = v___x_2988_;
goto v___jp_2894_;
}
}
}
else
{
lean_object* v_a_2991_; 
v_a_2991_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2982_, 1);
v___y_2912_ = v___y_2952_;
v___y_2913_ = v___y_2953_;
v___y_2914_ = v___x_2978_;
v___y_2915_ = v___y_2956_;
v___y_2916_ = v___y_2958_;
v___y_2917_ = v___y_2957_;
v___y_2918_ = v_a_2960_;
v_a_2919_ = v_a_2991_;
goto v___jp_2911_;
}
}
else
{
lean_object* v_a_2992_; 
lean_dec(v___y_2955_);
lean_dec_ref(v_cfg_2890_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
v_a_2992_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2979_, 1);
v___y_2912_ = v___y_2952_;
v___y_2913_ = v___y_2953_;
v___y_2914_ = v___x_2978_;
v___y_2915_ = v___y_2956_;
v___y_2916_ = v___y_2958_;
v___y_2917_ = v___y_2957_;
v___y_2918_ = v_a_2960_;
v_a_2919_ = v_a_2992_;
goto v___jp_2911_;
}
}
}
v___jp_2993_:
{
lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3001_ = l_Lean_trace_profiler;
v___x_3002_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2999_, v___x_3001_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_MVarId_exfalso(v___y_2996_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3005_, 0, v_a_3004_);
lean_ctor_set(v___x_3005_, 1, v___y_2997_);
v___x_3006_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2882_, v_ctx_2883_, v_cfg_2890_, v___x_3005_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
return v___x_3006_;
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec(v___y_2997_);
lean_dec_ref(v_cfg_2890_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
v_a_3007_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_3003_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3003_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
v___y_2952_ = v___y_2994_;
v___y_2953_ = v___y_2995_;
v___y_2954_ = v___y_2996_;
v___y_2955_ = v___y_2997_;
v___y_2956_ = v___y_2998_;
v___y_2957_ = v_a_3000_;
v___y_2958_ = v___y_2999_;
goto v___jp_2951_;
}
}
v___jp_3015_:
{
if (v___y_3016_ == 0)
{
if (lean_obj_tag(v_goals_2884_) == 1)
{
lean_object* v_tail_3017_; 
v_tail_3017_ = lean_ctor_get(v_goals_2884_, 1);
lean_inc(v_tail_3017_);
if (lean_obj_tag(v_tail_3017_) == 0)
{
lean_object* v_toApplyRulesConfig_3018_; uint8_t v_exfalso_3019_; 
v_toApplyRulesConfig_3018_ = lean_ctor_get(v_cfg_2890_, 0);
lean_inc_ref(v_toApplyRulesConfig_3018_);
v_exfalso_3019_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3018_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_3018_);
if (v_exfalso_3019_ == 1)
{
lean_object* v_options_3020_; lean_object* v_head_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref_known(v___x_2891_, 1);
v_options_3020_ = lean_ctor_get(v_a_2887_, 2);
v_head_3021_ = lean_ctor_get(v_goals_2884_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_goals_2884_);
if (v_isSharedCheck_3046_ == 0)
{
lean_object* v_unused_3047_; 
v_unused_3047_ = lean_ctor_get(v_goals_2884_, 1);
lean_dec(v_unused_3047_);
v___x_3023_ = v_goals_2884_;
v_isShared_3024_ = v_isSharedCheck_3046_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_head_3021_);
lean_dec(v_goals_2884_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3046_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v_inheritedTraceOptions_3025_; uint8_t v_hasTrace_3026_; uint8_t v___x_3027_; 
v_inheritedTraceOptions_3025_ = lean_ctor_get(v_a_2887_, 13);
v_hasTrace_3026_ = lean_ctor_get_uint8(v_options_3020_, sizeof(void*)*1);
v___x_3027_ = lean_bool_not(v_hasTrace_3026_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
lean_del_object(v___x_3023_);
v___x_3028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_3029_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
if (v_hasTrace_3026_ == 0)
{
v___y_2994_ = v___x_3029_;
v___y_2995_ = v___x_3028_;
v___y_2996_ = v_head_3021_;
v___y_2997_ = v_tail_3017_;
v___y_2998_ = v_exfalso_3019_;
v___y_2999_ = v_options_3020_;
v_a_3000_ = v_hasTrace_3026_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3030_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_3031_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3025_, v_options_3020_, v___x_3030_);
if (v___x_3031_ == 0)
{
v___y_2994_ = v___x_3029_;
v___y_2995_ = v___x_3028_;
v___y_2996_ = v_head_3021_;
v___y_2997_ = v_tail_3017_;
v___y_2998_ = v_exfalso_3019_;
v___y_2999_ = v_options_3020_;
v_a_3000_ = v___x_3031_;
goto v___jp_2993_;
}
else
{
v___y_2952_ = v___x_3029_;
v___y_2953_ = v___x_3028_;
v___y_2954_ = v_head_3021_;
v___y_2955_ = v_tail_3017_;
v___y_2956_ = v_exfalso_3019_;
v___y_2957_ = v___x_3031_;
v___y_2958_ = v_options_3020_;
goto v___jp_2951_;
}
}
}
else
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Lean_MVarId_exfalso(v_head_3021_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3035_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v_a_3033_);
v___x_3035_ = v___x_3023_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3033_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_tail_3017_);
v___x_3035_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; 
v___x_3036_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2882_, v_ctx_2883_, v_cfg_2890_, v___x_3035_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
return v___x_3036_;
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_del_object(v___x_3023_);
lean_dec_ref(v_cfg_2890_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
v_a_3038_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3032_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3032_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2884_, 2);
lean_dec_ref(v_cfg_2890_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
return v___x_2891_;
}
}
else
{
lean_dec(v_tail_3017_);
lean_dec_ref_known(v_goals_2884_, 2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_3050_, lean_object* v_lemmas_3051_, lean_object* v_ctx_3052_, lean_object* v_goals_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_3050_, v_lemmas_3051_, v_ctx_3052_, v_goals_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_3060_, lean_object* v_x_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
if (lean_obj_tag(v_x_3060_) == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = l_List_reverse___redArg(v_x_3061_);
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
else
{
lean_object* v_head_3069_; lean_object* v_tail_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3093_; 
v_head_3069_ = lean_ctor_get(v_x_3060_, 0);
v_tail_3070_ = lean_ctor_get(v_x_3060_, 1);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_x_3060_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3072_ = v_x_3060_;
v_isShared_3073_ = v_isSharedCheck_3093_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_tail_3070_);
lean_inc(v_head_3069_);
lean_dec(v_x_3060_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3093_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_Expr_applySymm(v_head_3069_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3077_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3075_);
lean_dec_ref_known(v___x_3074_, 1);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 1, v_x_3061_);
lean_ctor_set(v___x_3072_, 0, v_a_3075_);
v___x_3077_ = v___x_3072_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3075_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_x_3061_);
v___x_3077_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
v_x_3060_ = v_tail_3070_;
v_x_3061_ = v___x_3077_;
goto _start;
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3092_; 
lean_del_object(v___x_3072_);
v_a_3080_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3082_ = v___x_3074_;
v_isShared_3083_ = v_isSharedCheck_3092_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3074_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3092_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
uint8_t v___y_3085_; uint8_t v___x_3090_; 
v___x_3090_ = l_Lean_Exception_isInterrupt(v_a_3080_);
if (v___x_3090_ == 0)
{
uint8_t v___x_3091_; 
lean_inc(v_a_3080_);
v___x_3091_ = l_Lean_Exception_isRuntime(v_a_3080_);
v___y_3085_ = v___x_3091_;
goto v___jp_3084_;
}
else
{
v___y_3085_ = v___x_3090_;
goto v___jp_3084_;
}
v___jp_3084_:
{
if (v___y_3085_ == 0)
{
lean_del_object(v___x_3082_);
lean_dec(v_a_3080_);
v_x_3060_ = v_tail_3070_;
goto _start;
}
else
{
lean_object* v___x_3088_; 
lean_dec(v_tail_3070_);
lean_dec(v_x_3061_);
if (v_isShared_3083_ == 0)
{
v___x_3088_ = v___x_3082_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3080_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_3094_, lean_object* v_x_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_3094_, v_x_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_3102_, lean_object* v_hyps_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
if (v_symm_3102_ == 0)
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v_hyps_3103_);
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = lean_box(0);
lean_inc(v_hyps_3103_);
v___x_3111_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_3103_, v___x_3110_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3120_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3114_ = v___x_3111_;
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = l_List_appendTR___redArg(v_hyps_3103_, v_a_3112_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3116_);
v___x_3118_ = v___x_3114_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
else
{
lean_dec(v_hyps_3103_);
return v___x_3111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3121_, lean_object* v_hyps_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_){
_start:
{
uint8_t v_symm_boxed_3128_; lean_object* v_res_3129_; 
v_symm_boxed_3128_ = lean_unbox(v_symm_3121_);
v_res_3129_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3128_, v_hyps_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3130_, size_t v_sz_3131_, size_t v_i_3132_, lean_object* v_b_3133_){
_start:
{
uint8_t v___x_3135_; 
v___x_3135_ = lean_usize_dec_lt(v_i_3132_, v_sz_3131_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; 
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_b_3133_);
return v___x_3136_;
}
else
{
lean_object* v_snd_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3156_; 
v_snd_3137_ = lean_ctor_get(v_b_3133_, 1);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_b_3133_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; 
v_unused_3157_ = lean_ctor_get(v_b_3133_, 0);
lean_dec(v_unused_3157_);
v___x_3139_ = v_b_3133_;
v_isShared_3140_ = v_isSharedCheck_3156_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_snd_3137_);
lean_dec(v_b_3133_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3156_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; lean_object* v_a_3143_; lean_object* v_a_3150_; 
v___x_3141_ = lean_box(0);
v_a_3150_ = lean_array_uget_borrowed(v_as_3130_, v_i_3132_);
if (lean_obj_tag(v_a_3150_) == 0)
{
v_a_3143_ = v_snd_3137_;
goto v___jp_3142_;
}
else
{
lean_object* v_val_3151_; uint8_t v___x_3152_; uint8_t v___x_3153_; 
v_val_3151_ = lean_ctor_get(v_a_3150_, 0);
v___x_3152_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3151_);
v___x_3153_ = lean_bool_not(v___x_3152_);
if (v___x_3153_ == 0)
{
v_a_3143_ = v_snd_3137_;
goto v___jp_3142_;
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
lean_inc(v_val_3151_);
v___x_3154_ = l_Lean_LocalDecl_toExpr(v_val_3151_);
v___x_3155_ = lean_array_push(v_snd_3137_, v___x_3154_);
v_a_3143_ = v___x_3155_;
goto v___jp_3142_;
}
}
v___jp_3142_:
{
lean_object* v___x_3145_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 1, v_a_3143_);
lean_ctor_set(v___x_3139_, 0, v___x_3141_);
v___x_3145_ = v___x_3139_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_a_3143_);
v___x_3145_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
size_t v___x_3146_; size_t v___x_3147_; 
v___x_3146_ = ((size_t)1ULL);
v___x_3147_ = lean_usize_add(v_i_3132_, v___x_3146_);
v_i_3132_ = v___x_3147_;
v_b_3133_ = v___x_3145_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3158_, lean_object* v_sz_3159_, lean_object* v_i_3160_, lean_object* v_b_3161_, lean_object* v___y_3162_){
_start:
{
size_t v_sz_boxed_3163_; size_t v_i_boxed_3164_; lean_object* v_res_3165_; 
v_sz_boxed_3163_ = lean_unbox_usize(v_sz_3159_);
lean_dec(v_sz_3159_);
v_i_boxed_3164_ = lean_unbox_usize(v_i_3160_);
lean_dec(v_i_3160_);
v_res_3165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3158_, v_sz_boxed_3163_, v_i_boxed_3164_, v_b_3161_);
lean_dec_ref(v_as_3158_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3166_, size_t v_sz_3167_, size_t v_i_3168_, lean_object* v_b_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
uint8_t v___x_3177_; 
v___x_3177_ = lean_usize_dec_lt(v_i_3168_, v_sz_3167_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; 
v___x_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3178_, 0, v_b_3169_);
return v___x_3178_;
}
else
{
lean_object* v_snd_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3198_; 
v_snd_3179_ = lean_ctor_get(v_b_3169_, 1);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_b_3169_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; 
v_unused_3199_ = lean_ctor_get(v_b_3169_, 0);
lean_dec(v_unused_3199_);
v___x_3181_ = v_b_3169_;
v_isShared_3182_ = v_isSharedCheck_3198_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_snd_3179_);
lean_dec(v_b_3169_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3198_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3183_; lean_object* v_a_3185_; lean_object* v_a_3192_; 
v___x_3183_ = lean_box(0);
v_a_3192_ = lean_array_uget_borrowed(v_as_3166_, v_i_3168_);
if (lean_obj_tag(v_a_3192_) == 0)
{
v_a_3185_ = v_snd_3179_;
goto v___jp_3184_;
}
else
{
lean_object* v_val_3193_; uint8_t v___x_3194_; uint8_t v___x_3195_; 
v_val_3193_ = lean_ctor_get(v_a_3192_, 0);
v___x_3194_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3193_);
v___x_3195_ = lean_bool_not(v___x_3194_);
if (v___x_3195_ == 0)
{
v_a_3185_ = v_snd_3179_;
goto v___jp_3184_;
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
lean_inc(v_val_3193_);
v___x_3196_ = l_Lean_LocalDecl_toExpr(v_val_3193_);
v___x_3197_ = lean_array_push(v_snd_3179_, v___x_3196_);
v_a_3185_ = v___x_3197_;
goto v___jp_3184_;
}
}
v___jp_3184_:
{
lean_object* v___x_3187_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 1, v_a_3185_);
lean_ctor_set(v___x_3181_, 0, v___x_3183_);
v___x_3187_ = v___x_3181_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3183_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_a_3185_);
v___x_3187_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
size_t v___x_3188_; size_t v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = ((size_t)1ULL);
v___x_3189_ = lean_usize_add(v_i_3168_, v___x_3188_);
v___x_3190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3166_, v_sz_3167_, v___x_3189_, v___x_3187_);
return v___x_3190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3200_, lean_object* v_sz_3201_, lean_object* v_i_3202_, lean_object* v_b_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
size_t v_sz_boxed_3211_; size_t v_i_boxed_3212_; lean_object* v_res_3213_; 
v_sz_boxed_3211_ = lean_unbox_usize(v_sz_3201_);
lean_dec(v_sz_3201_);
v_i_boxed_3212_ = lean_unbox_usize(v_i_3202_);
lean_dec(v_i_3202_);
v_res_3213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3200_, v_sz_boxed_3211_, v_i_boxed_3212_, v_b_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec_ref(v_as_3200_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3214_, size_t v_sz_3215_, size_t v_i_3216_, lean_object* v_b_3217_){
_start:
{
uint8_t v___x_3219_; 
v___x_3219_ = lean_usize_dec_lt(v_i_3216_, v_sz_3215_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3220_, 0, v_b_3217_);
return v___x_3220_;
}
else
{
lean_object* v_snd_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3240_; 
v_snd_3221_ = lean_ctor_get(v_b_3217_, 1);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_b_3217_);
if (v_isSharedCheck_3240_ == 0)
{
lean_object* v_unused_3241_; 
v_unused_3241_ = lean_ctor_get(v_b_3217_, 0);
lean_dec(v_unused_3241_);
v___x_3223_ = v_b_3217_;
v_isShared_3224_ = v_isSharedCheck_3240_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_snd_3221_);
lean_dec(v_b_3217_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3240_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; lean_object* v_a_3227_; lean_object* v_a_3234_; 
v___x_3225_ = lean_box(0);
v_a_3234_ = lean_array_uget_borrowed(v_as_3214_, v_i_3216_);
if (lean_obj_tag(v_a_3234_) == 0)
{
v_a_3227_ = v_snd_3221_;
goto v___jp_3226_;
}
else
{
lean_object* v_val_3235_; uint8_t v___x_3236_; uint8_t v___x_3237_; 
v_val_3235_ = lean_ctor_get(v_a_3234_, 0);
v___x_3236_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3235_);
v___x_3237_ = lean_bool_not(v___x_3236_);
if (v___x_3237_ == 0)
{
v_a_3227_ = v_snd_3221_;
goto v___jp_3226_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
lean_inc(v_val_3235_);
v___x_3238_ = l_Lean_LocalDecl_toExpr(v_val_3235_);
v___x_3239_ = lean_array_push(v_snd_3221_, v___x_3238_);
v_a_3227_ = v___x_3239_;
goto v___jp_3226_;
}
}
v___jp_3226_:
{
lean_object* v___x_3229_; 
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 1, v_a_3227_);
lean_ctor_set(v___x_3223_, 0, v___x_3225_);
v___x_3229_ = v___x_3223_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_a_3227_);
v___x_3229_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
size_t v___x_3230_; size_t v___x_3231_; 
v___x_3230_ = ((size_t)1ULL);
v___x_3231_ = lean_usize_add(v_i_3216_, v___x_3230_);
v_i_3216_ = v___x_3231_;
v_b_3217_ = v___x_3229_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3242_, lean_object* v_sz_3243_, lean_object* v_i_3244_, lean_object* v_b_3245_, lean_object* v___y_3246_){
_start:
{
size_t v_sz_boxed_3247_; size_t v_i_boxed_3248_; lean_object* v_res_3249_; 
v_sz_boxed_3247_ = lean_unbox_usize(v_sz_3243_);
lean_dec(v_sz_3243_);
v_i_boxed_3248_ = lean_unbox_usize(v_i_3244_);
lean_dec(v_i_3244_);
v_res_3249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3242_, v_sz_boxed_3247_, v_i_boxed_3248_, v_b_3245_);
lean_dec_ref(v_as_3242_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3250_, size_t v_sz_3251_, size_t v_i_3252_, lean_object* v_b_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
uint8_t v___x_3261_; 
v___x_3261_ = lean_usize_dec_lt(v_i_3252_, v_sz_3251_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; 
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v_b_3253_);
return v___x_3262_;
}
else
{
lean_object* v_snd_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3282_; 
v_snd_3263_ = lean_ctor_get(v_b_3253_, 1);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_b_3253_);
if (v_isSharedCheck_3282_ == 0)
{
lean_object* v_unused_3283_; 
v_unused_3283_ = lean_ctor_get(v_b_3253_, 0);
lean_dec(v_unused_3283_);
v___x_3265_ = v_b_3253_;
v_isShared_3266_ = v_isSharedCheck_3282_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_snd_3263_);
lean_dec(v_b_3253_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3282_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3267_; lean_object* v_a_3269_; lean_object* v_a_3276_; 
v___x_3267_ = lean_box(0);
v_a_3276_ = lean_array_uget_borrowed(v_as_3250_, v_i_3252_);
if (lean_obj_tag(v_a_3276_) == 0)
{
v_a_3269_ = v_snd_3263_;
goto v___jp_3268_;
}
else
{
lean_object* v_val_3277_; uint8_t v___x_3278_; uint8_t v___x_3279_; 
v_val_3277_ = lean_ctor_get(v_a_3276_, 0);
v___x_3278_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3277_);
v___x_3279_ = lean_bool_not(v___x_3278_);
if (v___x_3279_ == 0)
{
v_a_3269_ = v_snd_3263_;
goto v___jp_3268_;
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_inc(v_val_3277_);
v___x_3280_ = l_Lean_LocalDecl_toExpr(v_val_3277_);
v___x_3281_ = lean_array_push(v_snd_3263_, v___x_3280_);
v_a_3269_ = v___x_3281_;
goto v___jp_3268_;
}
}
v___jp_3268_:
{
lean_object* v___x_3271_; 
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 1, v_a_3269_);
lean_ctor_set(v___x_3265_, 0, v___x_3267_);
v___x_3271_ = v___x_3265_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v_a_3269_);
v___x_3271_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
size_t v___x_3272_; size_t v___x_3273_; lean_object* v___x_3274_; 
v___x_3272_ = ((size_t)1ULL);
v___x_3273_ = lean_usize_add(v_i_3252_, v___x_3272_);
v___x_3274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3250_, v_sz_3251_, v___x_3273_, v___x_3271_);
return v___x_3274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3284_, lean_object* v_sz_3285_, lean_object* v_i_3286_, lean_object* v_b_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
size_t v_sz_boxed_3295_; size_t v_i_boxed_3296_; lean_object* v_res_3297_; 
v_sz_boxed_3295_ = lean_unbox_usize(v_sz_3285_);
lean_dec(v_sz_3285_);
v_i_boxed_3296_ = lean_unbox_usize(v_i_3286_);
lean_dec(v_i_3286_);
v_res_3297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3284_, v_sz_boxed_3295_, v_i_boxed_3296_, v_b_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec_ref(v_as_3284_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3298_, lean_object* v_n_3299_, lean_object* v_b_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
if (lean_obj_tag(v_n_3299_) == 0)
{
lean_object* v_cs_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; size_t v_sz_3311_; size_t v___x_3312_; lean_object* v___x_3313_; 
v_cs_3308_ = lean_ctor_get(v_n_3299_, 0);
v___x_3309_ = lean_box(0);
v___x_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
lean_ctor_set(v___x_3310_, 1, v_b_3300_);
v_sz_3311_ = lean_array_size(v_cs_3308_);
v___x_3312_ = ((size_t)0ULL);
v___x_3313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3298_, v_cs_3308_, v_sz_3311_, v___x_3312_, v___x_3310_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3328_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3316_ = v___x_3313_;
v_isShared_3317_ = v_isSharedCheck_3328_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3328_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v_fst_3318_; 
v_fst_3318_ = lean_ctor_get(v_a_3314_, 0);
if (lean_obj_tag(v_fst_3318_) == 0)
{
lean_object* v_snd_3319_; lean_object* v___x_3320_; lean_object* v___x_3322_; 
v_snd_3319_ = lean_ctor_get(v_a_3314_, 1);
lean_inc(v_snd_3319_);
lean_dec(v_a_3314_);
v___x_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3320_, 0, v_snd_3319_);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v___x_3320_);
v___x_3322_ = v___x_3316_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
else
{
lean_object* v_val_3324_; lean_object* v___x_3326_; 
lean_inc_ref(v_fst_3318_);
lean_dec(v_a_3314_);
v_val_3324_ = lean_ctor_get(v_fst_3318_, 0);
lean_inc(v_val_3324_);
lean_dec_ref_known(v_fst_3318_, 1);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v_val_3324_);
v___x_3326_ = v___x_3316_;
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
v_a_3329_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3313_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3313_);
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
else
{
lean_object* v_vs_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; size_t v_sz_3340_; size_t v___x_3341_; lean_object* v___x_3342_; 
v_vs_3337_ = lean_ctor_get(v_n_3299_, 0);
v___x_3338_ = lean_box(0);
v___x_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
lean_ctor_set(v___x_3339_, 1, v_b_3300_);
v_sz_3340_ = lean_array_size(v_vs_3337_);
v___x_3341_ = ((size_t)0ULL);
v___x_3342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3337_, v_sz_3340_, v___x_3341_, v___x_3339_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3357_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3357_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3357_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v_fst_3347_; 
v_fst_3347_ = lean_ctor_get(v_a_3343_, 0);
if (lean_obj_tag(v_fst_3347_) == 0)
{
lean_object* v_snd_3348_; lean_object* v___x_3349_; lean_object* v___x_3351_; 
v_snd_3348_ = lean_ctor_get(v_a_3343_, 1);
lean_inc(v_snd_3348_);
lean_dec(v_a_3343_);
v___x_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_snd_3348_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3349_);
v___x_3351_ = v___x_3345_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
else
{
lean_object* v_val_3353_; lean_object* v___x_3355_; 
lean_inc_ref(v_fst_3347_);
lean_dec(v_a_3343_);
v_val_3353_ = lean_ctor_get(v_fst_3347_, 0);
lean_inc(v_val_3353_);
lean_dec_ref_known(v_fst_3347_, 1);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v_val_3353_);
v___x_3355_ = v___x_3345_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_val_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
v_a_3358_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3342_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3342_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3366_, lean_object* v_as_3367_, size_t v_sz_3368_, size_t v_i_3369_, lean_object* v_b_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
uint8_t v___x_3378_; 
v___x_3378_ = lean_usize_dec_lt(v_i_3369_, v_sz_3368_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v_b_3370_);
return v___x_3379_;
}
else
{
lean_object* v_snd_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3414_; 
v_snd_3380_ = lean_ctor_get(v_b_3370_, 1);
v_isSharedCheck_3414_ = !lean_is_exclusive(v_b_3370_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; 
v_unused_3415_ = lean_ctor_get(v_b_3370_, 0);
lean_dec(v_unused_3415_);
v___x_3382_ = v_b_3370_;
v_isShared_3383_ = v_isSharedCheck_3414_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_snd_3380_);
lean_dec(v_b_3370_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3414_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v_a_3384_; lean_object* v___x_3385_; 
v_a_3384_ = lean_array_uget_borrowed(v_as_3367_, v_i_3369_);
lean_inc(v_snd_3380_);
v___x_3385_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3366_, v_a_3384_, v_snd_3380_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3405_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3405_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3405_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
if (lean_obj_tag(v_a_3386_) == 0)
{
lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3390_, 0, v_a_3386_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3390_);
v___x_3392_ = v___x_3382_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_snd_3380_);
v___x_3392_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3394_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3392_);
v___x_3394_ = v___x_3388_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3398_; lean_object* v___x_3400_; 
lean_del_object(v___x_3388_);
lean_dec(v_snd_3380_);
v_a_3397_ = lean_ctor_get(v_a_3386_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v_a_3386_, 1);
v___x_3398_ = lean_box(0);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 1, v_a_3397_);
lean_ctor_set(v___x_3382_, 0, v___x_3398_);
v___x_3400_ = v___x_3382_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_a_3397_);
v___x_3400_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
size_t v___x_3401_; size_t v___x_3402_; 
v___x_3401_ = ((size_t)1ULL);
v___x_3402_ = lean_usize_add(v_i_3369_, v___x_3401_);
v_i_3369_ = v___x_3402_;
v_b_3370_ = v___x_3400_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_del_object(v___x_3382_);
lean_dec(v_snd_3380_);
v_a_3406_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3385_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3385_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3416_, lean_object* v_as_3417_, lean_object* v_sz_3418_, lean_object* v_i_3419_, lean_object* v_b_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
size_t v_sz_boxed_3428_; size_t v_i_boxed_3429_; lean_object* v_res_3430_; 
v_sz_boxed_3428_ = lean_unbox_usize(v_sz_3418_);
lean_dec(v_sz_3418_);
v_i_boxed_3429_ = lean_unbox_usize(v_i_3419_);
lean_dec(v_i_3419_);
v_res_3430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3416_, v_as_3417_, v_sz_boxed_3428_, v_i_boxed_3429_, v_b_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec_ref(v_as_3417_);
lean_dec_ref(v_init_3416_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3431_, lean_object* v_n_3432_, lean_object* v_b_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3431_, v_n_3432_, v_b_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec_ref(v_n_3432_);
lean_dec_ref(v_init_3431_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3442_, lean_object* v_init_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_root_3451_; lean_object* v_tail_3452_; lean_object* v___x_3453_; 
v_root_3451_ = lean_ctor_get(v_t_3442_, 0);
v_tail_3452_ = lean_ctor_get(v_t_3442_, 1);
lean_inc_ref(v_init_3443_);
v___x_3453_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3443_, v_root_3451_, v_init_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec_ref(v_init_3443_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3490_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3456_ = v___x_3453_;
v_isShared_3457_ = v_isSharedCheck_3490_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3453_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3490_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
if (lean_obj_tag(v_a_3454_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3460_; 
v_a_3458_ = lean_ctor_get(v_a_3454_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v_a_3454_, 1);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v_a_3458_);
v___x_3460_ = v___x_3456_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3458_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; size_t v_sz_3465_; size_t v___x_3466_; lean_object* v___x_3467_; 
lean_del_object(v___x_3456_);
v_a_3462_ = lean_ctor_get(v_a_3454_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v_a_3454_, 1);
v___x_3463_ = lean_box(0);
v___x_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v_a_3462_);
v_sz_3465_ = lean_array_size(v_tail_3452_);
v___x_3466_ = ((size_t)0ULL);
v___x_3467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3452_, v_sz_3465_, v___x_3466_, v___x_3464_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3481_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3470_ = v___x_3467_;
v_isShared_3471_ = v_isSharedCheck_3481_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3481_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v_fst_3472_; 
v_fst_3472_ = lean_ctor_get(v_a_3468_, 0);
if (lean_obj_tag(v_fst_3472_) == 0)
{
lean_object* v_snd_3473_; lean_object* v___x_3475_; 
v_snd_3473_ = lean_ctor_get(v_a_3468_, 1);
lean_inc(v_snd_3473_);
lean_dec(v_a_3468_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v_snd_3473_);
v___x_3475_ = v___x_3470_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_snd_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
else
{
lean_object* v_val_3477_; lean_object* v___x_3479_; 
lean_inc_ref(v_fst_3472_);
lean_dec(v_a_3468_);
v_val_3477_ = lean_ctor_get(v_fst_3472_, 0);
lean_inc(v_val_3477_);
lean_dec_ref_known(v_fst_3472_, 1);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v_val_3477_);
v___x_3479_ = v___x_3470_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_val_3477_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
v_a_3482_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3467_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3467_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
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
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
v_a_3491_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3453_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3453_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3499_, lean_object* v_init_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3499_, v_init_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v_t_3499_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v_lctx_3518_; lean_object* v_decls_3519_; lean_object* v_hs_3520_; lean_object* v___x_3521_; 
v_lctx_3518_ = lean_ctor_get(v___y_3513_, 2);
v_decls_3519_ = lean_ctor_get(v_lctx_3518_, 1);
v_hs_3520_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3521_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3519_, v_hs_3520_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3530_, lean_object* v_cfg_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
if (v_only_3530_ == 0)
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_toApplyRulesConfig_3540_; lean_object* v_a_3541_; uint8_t v_symm_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v_toApplyRulesConfig_3540_ = lean_ctor_get(v_cfg_3531_, 0);
v_a_3541_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3539_, 1);
v_symm_3542_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3540_, sizeof(void*)*2 + 1);
v___x_3543_ = lean_array_to_list(v_a_3541_);
v___x_3544_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3542_, v___x_3543_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
return v___x_3544_;
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
v_a_3545_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3539_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3539_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = lean_box(0);
v___x_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
return v___x_3554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3555_, lean_object* v_cfg_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
uint8_t v_only_boxed_3564_; lean_object* v_res_3565_; 
v_only_boxed_3564_ = lean_unbox(v_only_3555_);
v_res_3565_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3564_, v_cfg_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec_ref(v_cfg_3556_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3566_, lean_object* v_lemmas_3567_, uint8_t v_only_3568_, lean_object* v_g_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_toApplyRulesConfig_3575_; uint8_t v_intro_3576_; uint8_t v_constructor_3577_; uint8_t v_suggestions_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3591_; 
v_toApplyRulesConfig_3575_ = lean_ctor_get(v_cfg_3566_, 0);
v_intro_3576_ = lean_ctor_get_uint8(v_cfg_3566_, sizeof(void*)*1 + 1);
v_constructor_3577_ = lean_ctor_get_uint8(v_cfg_3566_, sizeof(void*)*1 + 2);
v_suggestions_3578_ = lean_ctor_get_uint8(v_cfg_3566_, sizeof(void*)*1 + 3);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_cfg_3566_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3580_ = v_cfg_3566_;
v_isShared_3581_ = v_isSharedCheck_3591_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_toApplyRulesConfig_3575_);
lean_dec(v_cfg_3566_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3591_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3582_; lean_object* v_ctx_3583_; uint8_t v___x_3584_; lean_object* v___x_3586_; 
v___x_3582_ = lean_box(v_only_3568_);
v_ctx_3583_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3583_, 0, v___x_3582_);
v___x_3584_ = 0;
if (v_isShared_3581_ == 0)
{
v___x_3586_ = v___x_3580_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_toApplyRulesConfig_3575_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*1 + 1, v_intro_3576_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*1 + 2, v_constructor_3577_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*1 + 3, v_suggestions_3578_);
v___x_3586_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
lean_ctor_set_uint8(v___x_3586_, sizeof(void*)*1, v___x_3584_);
v___x_3587_ = lean_box(0);
v___x_3588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3588_, 0, v_g_3569_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
v___x_3589_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3586_, v_lemmas_3567_, v_ctx_3583_, v___x_3588_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_);
return v___x_3589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3592_, lean_object* v_lemmas_3593_, lean_object* v_only_3594_, lean_object* v_g_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
uint8_t v_only_boxed_3601_; lean_object* v_res_3602_; 
v_only_boxed_3601_ = lean_unbox(v_only_3594_);
v_res_3602_ = l_Lean_MVarId_applyRules(v_cfg_3592_, v_lemmas_3593_, v_only_boxed_3601_, v_g_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
lean_dec(v_a_3597_);
lean_dec_ref(v_a_3596_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3603_, size_t v_sz_3604_, size_t v_i_3605_, lean_object* v_b_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3603_, v_sz_3604_, v_i_3605_, v_b_3606_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3615_, lean_object* v_sz_3616_, lean_object* v_i_3617_, lean_object* v_b_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
size_t v_sz_boxed_3626_; size_t v_i_boxed_3627_; lean_object* v_res_3628_; 
v_sz_boxed_3626_ = lean_unbox_usize(v_sz_3616_);
lean_dec(v_sz_3616_);
v_i_boxed_3627_ = lean_unbox_usize(v_i_3617_);
lean_dec(v_i_3617_);
v_res_3628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3615_, v_sz_boxed_3626_, v_i_boxed_3627_, v_b_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v_as_3615_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3629_, size_t v_sz_3630_, size_t v_i_3631_, lean_object* v_b_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v___x_3640_; 
v___x_3640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3629_, v_sz_3630_, v_i_3631_, v_b_3632_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3641_, lean_object* v_sz_3642_, lean_object* v_i_3643_, lean_object* v_b_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
size_t v_sz_boxed_3652_; size_t v_i_boxed_3653_; lean_object* v_res_3654_; 
v_sz_boxed_3652_ = lean_unbox_usize(v_sz_3642_);
lean_dec(v_sz_3642_);
v_i_boxed_3653_ = lean_unbox_usize(v_i_3643_);
lean_dec(v_i_3643_);
v_res_3654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3641_, v_sz_boxed_3652_, v_i_boxed_3653_, v_b_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec_ref(v_as_3641_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v___x_3663_; uint8_t v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = lean_box(0);
v___x_3664_ = 1;
v___x_3665_ = l_Lean_Elab_Term_elabTerm(v_t_3655_, v___x_3663_, v___x_3664_, v___x_3664_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
lean_dec(v_a_3668_);
lean_dec_ref(v_a_3667_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
lean_object* v_ref_3680_; uint8_t v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v_ref_3680_ = lean_ctor_get(v___y_3677_, 5);
v___x_3681_ = 0;
v___x_3682_ = l_Lean_SourceInfo_fromRef(v_ref_3680_, v___x_3681_);
v___x_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
return v_res_3689_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3690_, lean_object* v_x_3691_){
_start:
{
if (lean_obj_tag(v_x_3691_) == 0)
{
uint8_t v___x_3692_; 
v___x_3692_ = 0;
return v___x_3692_;
}
else
{
lean_object* v_head_3693_; lean_object* v_tail_3694_; uint8_t v___x_3695_; 
v_head_3693_ = lean_ctor_get(v_x_3691_, 0);
v_tail_3694_ = lean_ctor_get(v_x_3691_, 1);
v___x_3695_ = lean_expr_eqv(v_a_3690_, v_head_3693_);
if (v___x_3695_ == 0)
{
v_x_3691_ = v_tail_3694_;
goto _start;
}
else
{
return v___x_3695_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3697_, lean_object* v_x_3698_){
_start:
{
uint8_t v_res_3699_; lean_object* v_r_3700_; 
v_res_3699_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3697_, v_x_3698_);
lean_dec(v_x_3698_);
lean_dec_ref(v_a_3697_);
v_r_3700_ = lean_box(v_res_3699_);
return v_r_3700_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3701_, lean_object* v_x_3702_){
_start:
{
uint8_t v___x_3703_; uint8_t v___x_3704_; 
v___x_3703_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3702_, v_ys_3701_);
v___x_3704_ = lean_bool_not(v___x_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3705_, lean_object* v_x_3706_){
_start:
{
uint8_t v_res_3707_; lean_object* v_r_3708_; 
v_res_3707_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3705_, v_x_3706_);
lean_dec_ref(v_x_3706_);
lean_dec(v_ys_3705_);
v_r_3708_ = lean_box(v_res_3707_);
return v_r_3708_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3709_, lean_object* v_ys_3710_){
_start:
{
lean_object* v___f_3711_; lean_object* v___x_3712_; 
v___f_3711_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3711_, 0, v_ys_3710_);
v___x_3712_ = l_List_filter___redArg(v___f_3711_, v_xs_3709_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3713_, lean_object* v_x_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
if (lean_obj_tag(v_x_3713_) == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = l_List_reverse___redArg(v_x_3714_);
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
return v___x_3723_;
}
else
{
lean_object* v_head_3724_; lean_object* v_tail_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3743_; 
v_head_3724_ = lean_ctor_get(v_x_3713_, 0);
v_tail_3725_ = lean_ctor_get(v_x_3713_, 1);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_x_3713_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3727_ = v_x_3713_;
v_isShared_3728_ = v_isSharedCheck_3743_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_tail_3725_);
lean_inc(v_head_3724_);
lean_dec(v_x_3713_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3743_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3729_; 
v___x_3729_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3724_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3732_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 1, v_x_3714_);
lean_ctor_set(v___x_3727_, 0, v_a_3730_);
v___x_3732_ = v___x_3727_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3730_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_x_3714_);
v___x_3732_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
v_x_3713_ = v_tail_3725_;
v_x_3714_ = v___x_3732_;
goto _start;
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_del_object(v___x_3727_);
lean_dec(v_tail_3725_);
lean_dec(v_x_3714_);
v_a_3735_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3729_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3729_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3744_, lean_object* v_x_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3744_, v_x_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3754_, uint8_t v_noDefaults_3755_, uint8_t v_star_3756_, lean_object* v_cfg_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
if (v_noDefaults_3755_ == 0)
{
goto v___jp_3765_;
}
else
{
uint8_t v___x_3784_; 
v___x_3784_ = lean_bool_not(v_star_3756_);
if (v___x_3784_ == 0)
{
goto v___jp_3765_;
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
lean_dec(v_remove_3754_);
v___x_3785_ = lean_box(0);
v___x_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
return v___x_3786_;
}
}
v___jp_3765_:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3766_, 1);
v___x_3768_ = lean_box(0);
v___x_3769_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3754_, v___x_3768_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_toApplyRulesConfig_3770_; lean_object* v_a_3771_; uint8_t v_symm_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v_toApplyRulesConfig_3770_ = lean_ctor_get(v_cfg_3757_, 0);
v_a_3771_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3771_);
lean_dec_ref_known(v___x_3769_, 1);
v_symm_3772_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3770_, sizeof(void*)*2 + 1);
v___x_3773_ = lean_array_to_list(v_a_3767_);
v___x_3774_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3773_, v_a_3771_);
v___x_3775_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3772_, v___x_3774_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
return v___x_3775_;
}
else
{
lean_dec(v_a_3767_);
return v___x_3769_;
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec(v_remove_3754_);
v_a_3776_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3766_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3766_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3787_, lean_object* v_noDefaults_3788_, lean_object* v_star_3789_, lean_object* v_cfg_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
uint8_t v_noDefaults_boxed_3798_; uint8_t v_star_boxed_3799_; lean_object* v_res_3800_; 
v_noDefaults_boxed_3798_ = lean_unbox(v_noDefaults_3788_);
v_star_boxed_3799_ = lean_unbox(v_star_3789_);
v_res_3800_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3787_, v_noDefaults_boxed_3798_, v_star_boxed_3799_, v_cfg_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec_ref(v_cfg_3790_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3801_, size_t v_i_3802_, size_t v_stop_3803_, lean_object* v_b_3804_){
_start:
{
uint8_t v___x_3805_; 
v___x_3805_ = lean_usize_dec_eq(v_i_3802_, v_stop_3803_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; lean_object* v___x_3807_; size_t v___x_3808_; size_t v___x_3809_; 
v___x_3806_ = lean_array_uget_borrowed(v_as_3801_, v_i_3802_);
v___x_3807_ = l_Array_append___redArg(v_b_3804_, v___x_3806_);
v___x_3808_ = ((size_t)1ULL);
v___x_3809_ = lean_usize_add(v_i_3802_, v___x_3808_);
v_i_3802_ = v___x_3809_;
v_b_3804_ = v___x_3807_;
goto _start;
}
else
{
return v_b_3804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3811_, lean_object* v_i_3812_, lean_object* v_stop_3813_, lean_object* v_b_3814_){
_start:
{
size_t v_i_boxed_3815_; size_t v_stop_boxed_3816_; lean_object* v_res_3817_; 
v_i_boxed_3815_ = lean_unbox_usize(v_i_3812_);
lean_dec(v_i_3812_);
v_stop_boxed_3816_ = lean_unbox_usize(v_stop_3813_);
lean_dec(v_stop_3813_);
v_res_3817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3811_, v_i_boxed_3815_, v_stop_boxed_3816_, v_b_3814_);
lean_dec_ref(v_as_3811_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
if (lean_obj_tag(v_a_3818_) == 0)
{
lean_object* v___x_3820_; 
v___x_3820_ = l_List_reverse___redArg(v_a_3819_);
return v___x_3820_;
}
else
{
lean_object* v_head_3821_; lean_object* v_tail_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3831_; 
v_head_3821_ = lean_ctor_get(v_a_3818_, 0);
v_tail_3822_ = lean_ctor_get(v_a_3818_, 1);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_a_3818_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3824_ = v_a_3818_;
v_isShared_3825_ = v_isSharedCheck_3831_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_tail_3822_);
lean_inc(v_head_3821_);
lean_dec(v_a_3818_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3831_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3826_; lean_object* v___x_3828_; 
v___x_3826_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3826_, 0, v_head_3821_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 1, v_a_3819_);
lean_ctor_set(v___x_3824_, 0, v___x_3826_);
v___x_3828_ = v___x_3824_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_a_3819_);
v___x_3828_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
v_a_3818_ = v_tail_3822_;
v_a_3819_ = v___x_3828_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3832_, size_t v_i_3833_, lean_object* v_bs_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
uint8_t v___x_3838_; 
v___x_3838_ = lean_usize_dec_lt(v_i_3833_, v_sz_3832_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; 
v___x_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3839_, 0, v_bs_3834_);
return v___x_3839_;
}
else
{
lean_object* v_v_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v_v_3840_ = lean_array_uget_borrowed(v_bs_3834_, v_i_3833_);
v___x_3841_ = l_Lean_Syntax_getId(v_v_3840_);
v___x_3842_ = l_Lean_labelled(v___x_3841_, v___y_3835_, v___y_3836_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3844_; lean_object* v_bs_x27_3845_; size_t v___x_3846_; size_t v___x_3847_; lean_object* v___x_3848_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref_known(v___x_3842_, 1);
v___x_3844_ = lean_unsigned_to_nat(0u);
v_bs_x27_3845_ = lean_array_uset(v_bs_3834_, v_i_3833_, v___x_3844_);
v___x_3846_ = ((size_t)1ULL);
v___x_3847_ = lean_usize_add(v_i_3833_, v___x_3846_);
v___x_3848_ = lean_array_uset(v_bs_x27_3845_, v_i_3833_, v_a_3843_);
v_i_3833_ = v___x_3847_;
v_bs_3834_ = v___x_3848_;
goto _start;
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec_ref(v_bs_3834_);
v_a_3850_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3842_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3842_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3858_, lean_object* v_i_3859_, lean_object* v_bs_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
size_t v_sz_boxed_3864_; size_t v_i_boxed_3865_; lean_object* v_res_3866_; 
v_sz_boxed_3864_ = lean_unbox_usize(v_sz_3858_);
lean_dec(v_sz_3858_);
v_i_boxed_3865_ = lean_unbox_usize(v_i_3859_);
lean_dec(v_i_3859_);
v_res_3866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3864_, v_i_boxed_3865_, v_bs_3860_, v___y_3861_, v___y_3862_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3867_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3885_, lean_object* v_a_3886_){
_start:
{
if (lean_obj_tag(v_a_3885_) == 0)
{
lean_object* v___x_3887_; 
v___x_3887_ = l_List_reverse___redArg(v_a_3886_);
return v___x_3887_;
}
else
{
lean_object* v_head_3888_; lean_object* v_tail_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3898_; 
v_head_3888_ = lean_ctor_get(v_a_3885_, 0);
v_tail_3889_ = lean_ctor_get(v_a_3885_, 1);
v_isSharedCheck_3898_ = !lean_is_exclusive(v_a_3885_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3891_ = v_a_3885_;
v_isShared_3892_ = v_isSharedCheck_3898_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_tail_3889_);
lean_inc(v_head_3888_);
lean_dec(v_a_3885_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3898_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___f_3893_; lean_object* v___x_3895_; 
v___f_3893_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3893_, 0, v_head_3888_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 1, v_a_3886_);
lean_ctor_set(v___x_3891_, 0, v___f_3893_);
v___x_3895_ = v___x_3891_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___f_3893_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_a_3886_);
v___x_3895_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
v_a_3885_ = v_tail_3889_;
v_a_3886_ = v___x_3895_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3901_ = l_Lean_stringToMessageData(v___x_3900_);
return v___x_3901_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3904_ = l_String_toRawSubstring_x27(v___x_3903_);
return v___x_3904_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3908_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3909_ = l_String_toRawSubstring_x27(v___x_3908_);
return v___x_3909_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3914_ = l_String_toRawSubstring_x27(v___x_3913_);
return v___x_3914_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3919_ = l_String_toRawSubstring_x27(v___x_3918_);
return v___x_3919_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3949_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3950_ = l_Lean_stringToMessageData(v___x_3949_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3951_, uint8_t v_star_3952_, lean_object* v_add_3953_, lean_object* v_remove_3954_, lean_object* v_use_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; uint8_t v___y_3973_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___f_3996_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; 
v___x_3994_ = lean_box(v_noDefaults_3951_);
v___x_3995_ = lean_box(v_star_3952_);
lean_inc(v_remove_3954_);
v___f_3996_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3996_, 0, v_remove_3954_);
lean_closure_set(v___f_3996_, 1, v___x_3994_);
lean_closure_set(v___f_3996_, 2, v___x_3995_);
if (v_star_3952_ == 0)
{
v___y_4013_ = v_a_3956_;
v___y_4014_ = v_a_3957_;
v___y_4015_ = v_a_3958_;
v___y_4016_ = v_a_3959_;
goto v___jp_4012_;
}
else
{
uint8_t v___x_4075_; 
v___x_4075_ = lean_bool_not(v_noDefaults_3951_);
if (v___x_4075_ == 0)
{
v___y_4013_ = v_a_3956_;
v___y_4014_ = v_a_3957_;
v___y_4015_ = v_a_3958_;
v___y_4016_ = v_a_3959_;
goto v___jp_4012_;
}
else
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_dec_ref(v___f_3996_);
lean_dec_ref(v_use_3955_);
lean_dec(v_remove_3954_);
lean_dec(v_add_3953_);
v___x_4076_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_4077_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_4076_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
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
}
v___jp_3961_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___y_3962_);
lean_ctor_set(v___x_3964_, 1, v___y_3963_);
v___x_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
return v___x_3965_;
}
v___jp_3966_:
{
if (v___y_3973_ == 0)
{
v___y_3962_ = v___y_3968_;
v___y_3963_ = v___y_3970_;
goto v___jp_3961_;
}
else
{
uint8_t v___x_3974_; 
v___x_3974_ = lean_bool_not(v_star_3952_);
if (v___x_3974_ == 0)
{
v___y_3962_ = v___y_3968_;
v___y_3963_ = v___y_3970_;
goto v___jp_3961_;
}
else
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3968_);
v___x_3975_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3976_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3975_, v___y_3971_, v___y_3969_, v___y_3972_, v___y_3967_);
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3976_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3976_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
}
v___jp_3985_:
{
uint8_t v___x_3992_; uint8_t v___x_3993_; 
v___x_3992_ = l_List_isEmpty___redArg(v_remove_3954_);
lean_dec(v_remove_3954_);
v___x_3993_ = lean_bool_not(v___x_3992_);
if (v___x_3993_ == 0)
{
v___y_3967_ = v___y_3986_;
v___y_3968_ = v___y_3991_;
v___y_3969_ = v___y_3987_;
v___y_3970_ = v___y_3988_;
v___y_3971_ = v___y_3989_;
v___y_3972_ = v___y_3990_;
v___y_3973_ = v___x_3993_;
goto v___jp_3966_;
}
else
{
v___y_3967_ = v___y_3986_;
v___y_3968_ = v___y_3991_;
v___y_3969_ = v___y_3987_;
v___y_3970_ = v___y_3988_;
v___y_3971_ = v___y_3989_;
v___y_3972_ = v___y_3990_;
v___y_3973_ = v_noDefaults_3951_;
goto v___jp_3966_;
}
}
v___jp_3997_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = lean_array_to_list(v___y_4004_);
lean_inc(v___y_4000_);
v___x_4006_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_4005_, v___y_4000_);
if (v_noDefaults_3951_ == 0)
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4007_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3953_, v___y_4000_);
v___x_4008_ = l_List_appendTR___redArg(v___x_4007_, v___x_4006_);
v___x_4009_ = l_List_appendTR___redArg(v___x_4008_, v___y_4001_);
v___y_3986_ = v___y_3998_;
v___y_3987_ = v___y_3999_;
v___y_3988_ = v___f_3996_;
v___y_3989_ = v___y_4002_;
v___y_3990_ = v___y_4003_;
v___y_3991_ = v___x_4009_;
goto v___jp_3985_;
}
else
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
lean_dec(v___y_4001_);
v___x_4010_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3953_, v___y_4000_);
v___x_4011_ = l_List_appendTR___redArg(v___x_4010_, v___x_4006_);
v___y_3986_ = v___y_3998_;
v___y_3987_ = v___y_3999_;
v___y_3988_ = v___f_3996_;
v___y_3989_ = v___y_4002_;
v___y_3990_ = v___y_4003_;
v___y_3991_ = v___x_4011_;
goto v___jp_3985_;
}
}
v___jp_4012_:
{
lean_object* v_ref_4017_; lean_object* v_quotContext_4018_; lean_object* v_currMacroScope_4019_; lean_object* v___x_4020_; lean_object* v_a_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v_a_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v_a_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; size_t v_sz_4033_; size_t v___x_4034_; lean_object* v___x_4035_; 
v_ref_4017_ = lean_ctor_get(v___y_4015_, 5);
v_quotContext_4018_ = lean_ctor_get(v___y_4015_, 10);
v_currMacroScope_4019_ = lean_ctor_get(v___y_4015_, 11);
v___x_4020_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
lean_inc(v_a_4021_);
lean_dec_ref(v___x_4020_);
v___x_4022_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_4023_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref(v___x_4023_);
v___x_4025_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_4019_, 2);
lean_inc_n(v_quotContext_4018_, 2);
v___x_4026_ = l_Lean_addMacroScope(v_quotContext_4018_, v___x_4025_, v_currMacroScope_4019_);
v___x_4027_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_4028_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref(v___x_4028_);
v___x_4030_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_4031_ = l_Lean_addMacroScope(v_quotContext_4018_, v___x_4030_, v_currMacroScope_4019_);
v___x_4032_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_4033_ = lean_array_size(v_use_3955_);
v___x_4034_ = ((size_t)0ULL);
v___x_4035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4033_, v___x_4034_, v_use_3955_, v___y_4015_, v___y_4016_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; uint8_t v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; uint8_t v___x_4061_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
lean_dec_ref_known(v___x_4035_, 1);
v___x_4037_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc_n(v_currMacroScope_4019_, 2);
lean_inc_n(v_quotContext_4018_, 2);
v___x_4038_ = l_Lean_addMacroScope(v_quotContext_4018_, v___x_4037_, v_currMacroScope_4019_);
v___x_4039_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_4040_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
v___x_4041_ = l_Lean_addMacroScope(v_quotContext_4018_, v___x_4040_, v_currMacroScope_4019_);
v___x_4042_ = 0;
v___x_4043_ = l_Lean_SourceInfo_fromRef(v_ref_4017_, v___x_4042_);
v___x_4044_ = lean_box(0);
v___x_4045_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_4046_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4043_);
lean_ctor_set(v___x_4046_, 1, v___x_4022_);
lean_ctor_set(v___x_4046_, 2, v___x_4026_);
lean_ctor_set(v___x_4046_, 3, v___x_4045_);
v___x_4047_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_4048_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4048_, 0, v_a_4021_);
lean_ctor_set(v___x_4048_, 1, v___x_4027_);
lean_ctor_set(v___x_4048_, 2, v___x_4031_);
lean_ctor_set(v___x_4048_, 3, v___x_4047_);
v___x_4049_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_4050_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4050_, 0, v_a_4024_);
lean_ctor_set(v___x_4050_, 1, v___x_4032_);
lean_ctor_set(v___x_4050_, 2, v___x_4038_);
lean_ctor_set(v___x_4050_, 3, v___x_4049_);
v___x_4051_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_4052_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4052_, 0, v_a_4029_);
lean_ctor_set(v___x_4052_, 1, v___x_4039_);
lean_ctor_set(v___x_4052_, 2, v___x_4041_);
lean_ctor_set(v___x_4052_, 3, v___x_4051_);
v___x_4053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
lean_ctor_set(v___x_4053_, 1, v___x_4044_);
v___x_4054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4050_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
v___x_4055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4048_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
v___x_4056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4046_);
lean_ctor_set(v___x_4056_, 1, v___x_4055_);
v___x_4057_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_4056_, v___x_4044_);
v___x_4058_ = lean_unsigned_to_nat(0u);
v___x_4059_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_4060_ = lean_array_get_size(v_a_4036_);
v___x_4061_ = lean_nat_dec_lt(v___x_4058_, v___x_4060_);
if (v___x_4061_ == 0)
{
lean_dec(v_a_4036_);
v___y_3998_ = v___y_4016_;
v___y_3999_ = v___y_4014_;
v___y_4000_ = v___x_4044_;
v___y_4001_ = v___x_4057_;
v___y_4002_ = v___y_4013_;
v___y_4003_ = v___y_4015_;
v___y_4004_ = v___x_4059_;
goto v___jp_3997_;
}
else
{
uint8_t v___x_4062_; 
v___x_4062_ = lean_nat_dec_le(v___x_4060_, v___x_4060_);
if (v___x_4062_ == 0)
{
if (v___x_4061_ == 0)
{
lean_dec(v_a_4036_);
v___y_3998_ = v___y_4016_;
v___y_3999_ = v___y_4014_;
v___y_4000_ = v___x_4044_;
v___y_4001_ = v___x_4057_;
v___y_4002_ = v___y_4013_;
v___y_4003_ = v___y_4015_;
v___y_4004_ = v___x_4059_;
goto v___jp_3997_;
}
else
{
size_t v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_usize_of_nat(v___x_4060_);
v___x_4064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4036_, v___x_4034_, v___x_4063_, v___x_4059_);
lean_dec(v_a_4036_);
v___y_3998_ = v___y_4016_;
v___y_3999_ = v___y_4014_;
v___y_4000_ = v___x_4044_;
v___y_4001_ = v___x_4057_;
v___y_4002_ = v___y_4013_;
v___y_4003_ = v___y_4015_;
v___y_4004_ = v___x_4064_;
goto v___jp_3997_;
}
}
else
{
size_t v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = lean_usize_of_nat(v___x_4060_);
v___x_4066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4036_, v___x_4034_, v___x_4065_, v___x_4059_);
lean_dec(v_a_4036_);
v___y_3998_ = v___y_4016_;
v___y_3999_ = v___y_4014_;
v___y_4000_ = v___x_4044_;
v___y_4001_ = v___x_4057_;
v___y_4002_ = v___y_4013_;
v___y_4003_ = v___y_4015_;
v___y_4004_ = v___x_4066_;
goto v___jp_3997_;
}
}
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
lean_dec(v___x_4031_);
lean_dec(v_a_4029_);
lean_dec(v___x_4026_);
lean_dec(v_a_4024_);
lean_dec(v_a_4021_);
lean_dec_ref(v___f_3996_);
lean_dec(v_remove_3954_);
lean_dec(v_add_3953_);
v_a_4067_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4035_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4035_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
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
