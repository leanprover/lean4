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
uint8_t v___x_14151__boxed_297_; uint8_t v___x_14152__boxed_298_; lean_object* v_res_299_; 
v___x_14151__boxed_297_ = lean_unbox(v___x_288_);
v___x_14152__boxed_298_ = lean_unbox(v___x_289_);
v_res_299_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_14151__boxed_297_, v___x_14152__boxed_298_, v_x_290_, v_x_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_e_424_){
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
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_e_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_427_);
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
v_result_505_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_fst_482_);
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
uint8_t v___x_14576__boxed_623_; lean_object* v_res_624_; 
v___x_14576__boxed_623_ = lean_unbox(v___x_615_);
v_res_624_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14576__boxed_623_, v_x_616_, v_x_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
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
uint8_t v___x_14653__boxed_667_; lean_object* v_res_668_; 
v___x_14653__boxed_667_ = lean_unbox(v___x_659_);
v_res_668_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14653__boxed_667_, v_x_660_, v_x_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
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
lean_object* v___x_690_; uint8_t v_foApprox_691_; uint8_t v_ctxApprox_692_; uint8_t v_quasiPatternApprox_693_; uint8_t v_constApprox_694_; uint8_t v_isDefEqStuckEx_695_; uint8_t v_unificationHints_696_; uint8_t v_proofIrrelevance_697_; uint8_t v_assignSyntheticOpaque_698_; uint8_t v_offsetCnstrs_699_; uint8_t v_etaStruct_700_; uint8_t v_univApprox_701_; uint8_t v_iota_702_; uint8_t v_beta_703_; uint8_t v_proj_704_; uint8_t v_zeta_705_; uint8_t v_zetaDelta_706_; uint8_t v_zetaUnused_707_; uint8_t v_zetaHave_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v___f_682_);
lean_dec_ref(v___x_681_);
lean_dec(v___x_679_);
v___x_690_ = l_Lean_Meta_Context_config(v___y_683_);
v_foApprox_691_ = lean_ctor_get_uint8(v___x_690_, 0);
v_ctxApprox_692_ = lean_ctor_get_uint8(v___x_690_, 1);
v_quasiPatternApprox_693_ = lean_ctor_get_uint8(v___x_690_, 2);
v_constApprox_694_ = lean_ctor_get_uint8(v___x_690_, 3);
v_isDefEqStuckEx_695_ = lean_ctor_get_uint8(v___x_690_, 4);
v_unificationHints_696_ = lean_ctor_get_uint8(v___x_690_, 5);
v_proofIrrelevance_697_ = lean_ctor_get_uint8(v___x_690_, 6);
v_assignSyntheticOpaque_698_ = lean_ctor_get_uint8(v___x_690_, 7);
v_offsetCnstrs_699_ = lean_ctor_get_uint8(v___x_690_, 8);
v_etaStruct_700_ = lean_ctor_get_uint8(v___x_690_, 10);
v_univApprox_701_ = lean_ctor_get_uint8(v___x_690_, 11);
v_iota_702_ = lean_ctor_get_uint8(v___x_690_, 12);
v_beta_703_ = lean_ctor_get_uint8(v___x_690_, 13);
v_proj_704_ = lean_ctor_get_uint8(v___x_690_, 14);
v_zeta_705_ = lean_ctor_get_uint8(v___x_690_, 15);
v_zetaDelta_706_ = lean_ctor_get_uint8(v___x_690_, 16);
v_zetaUnused_707_ = lean_ctor_get_uint8(v___x_690_, 17);
v_zetaHave_708_ = lean_ctor_get_uint8(v___x_690_, 18);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_746_ == 0)
{
v___x_710_ = v___x_690_;
v_isShared_711_ = v_isSharedCheck_746_;
goto v_resetjp_709_;
}
else
{
lean_dec(v___x_690_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_746_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
uint8_t v_trackZetaDelta_712_; lean_object* v_zetaDeltaSet_713_; lean_object* v_lctx_714_; lean_object* v_localInstances_715_; lean_object* v_defEqCtx_x3f_716_; lean_object* v_synthPendingDepth_717_; lean_object* v_canUnfold_x3f_718_; uint8_t v_univApprox_719_; uint8_t v_inTypeClassResolution_720_; uint8_t v_cacheInferType_721_; lean_object* v_config_723_; 
v_trackZetaDelta_712_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_713_ = lean_ctor_get(v___y_683_, 1);
v_lctx_714_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_715_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_716_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_717_ = lean_ctor_get(v___y_683_, 5);
v_canUnfold_x3f_718_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_719_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_720_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_721_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
if (v_isShared_711_ == 0)
{
v_config_723_ = v___x_710_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 0, v_foApprox_691_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 1, v_ctxApprox_692_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 2, v_quasiPatternApprox_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 3, v_constApprox_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 4, v_isDefEqStuckEx_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 5, v_unificationHints_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 6, v_proofIrrelevance_697_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 7, v_assignSyntheticOpaque_698_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 8, v_offsetCnstrs_699_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 10, v_etaStruct_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 11, v_univApprox_701_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 12, v_iota_702_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 13, v_beta_703_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 14, v_proj_704_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 15, v_zeta_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 16, v_zetaDelta_706_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 17, v_zetaUnused_707_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 18, v_zetaHave_708_);
v_config_723_ = v_reuseFailAlloc_745_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
uint64_t v___x_724_; uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; uint64_t v___x_728_; uint64_t v_key_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_ctor_set_uint8(v_config_723_, 9, v_transparency_674_);
v___x_724_ = l_Lean_Meta_Context_configKey(v___y_683_);
v___x_725_ = 3ULL;
v___x_726_ = lean_uint64_shift_right(v___x_724_, v___x_725_);
v___x_727_ = lean_uint64_shift_left(v___x_726_, v___x_725_);
v___x_728_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_674_);
v_key_729_ = lean_uint64_lor(v___x_727_, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_730_, 0, v_config_723_);
lean_ctor_set_uint64(v___x_730_, sizeof(void*)*1, v_key_729_);
lean_inc(v_canUnfold_x3f_718_);
lean_inc(v_synthPendingDepth_717_);
lean_inc(v_defEqCtx_x3f_716_);
lean_inc_ref(v_localInstances_715_);
lean_inc_ref(v_lctx_714_);
lean_inc(v_zetaDeltaSet_713_);
v___x_731_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_zetaDeltaSet_713_);
lean_ctor_set(v___x_731_, 2, v_lctx_714_);
lean_ctor_set(v___x_731_, 3, v_localInstances_715_);
lean_ctor_set(v___x_731_, 4, v_defEqCtx_x3f_716_);
lean_ctor_set(v___x_731_, 5, v_synthPendingDepth_717_);
lean_ctor_set(v___x_731_, 6, v_canUnfold_x3f_718_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*7, v_trackZetaDelta_712_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*7 + 1, v_univApprox_719_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*7 + 2, v_inTypeClassResolution_720_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*7 + 3, v_cacheInferType_721_);
v___x_732_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_731_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_731_, 7);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = lean_box(0);
v___x_735_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_689_, v_a_733_, v___x_734_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_744_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_744_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = l_List_reverse___redArg(v_a_736_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_740_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
return v___x_735_;
}
}
else
{
return v___x_732_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v_a_754_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v_a_769_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v_a_787_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v_a_799_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; 
v_inheritedTraceOptions_747_ = lean_ctor_get(v___y_685_, 13);
v___x_748_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_679_);
v___x_749_ = l_Lean_Name_append(v___x_748_, v___x_679_);
v___x_750_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_747_, v_options_688_, v___x_749_);
lean_dec(v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = l_Lean_trace_profiler;
v___x_922_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_688_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; uint8_t v_foApprox_924_; uint8_t v_ctxApprox_925_; uint8_t v_quasiPatternApprox_926_; uint8_t v_constApprox_927_; uint8_t v_isDefEqStuckEx_928_; uint8_t v_unificationHints_929_; uint8_t v_proofIrrelevance_930_; uint8_t v_assignSyntheticOpaque_931_; uint8_t v_offsetCnstrs_932_; uint8_t v_etaStruct_933_; uint8_t v_univApprox_934_; uint8_t v_iota_935_; uint8_t v_beta_936_; uint8_t v_proj_937_; uint8_t v_zeta_938_; uint8_t v_zetaDelta_939_; uint8_t v_zetaUnused_940_; uint8_t v_zetaHave_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref(v___f_682_);
lean_dec_ref(v___x_681_);
lean_dec(v___x_679_);
v___x_923_ = l_Lean_Meta_Context_config(v___y_683_);
v_foApprox_924_ = lean_ctor_get_uint8(v___x_923_, 0);
v_ctxApprox_925_ = lean_ctor_get_uint8(v___x_923_, 1);
v_quasiPatternApprox_926_ = lean_ctor_get_uint8(v___x_923_, 2);
v_constApprox_927_ = lean_ctor_get_uint8(v___x_923_, 3);
v_isDefEqStuckEx_928_ = lean_ctor_get_uint8(v___x_923_, 4);
v_unificationHints_929_ = lean_ctor_get_uint8(v___x_923_, 5);
v_proofIrrelevance_930_ = lean_ctor_get_uint8(v___x_923_, 6);
v_assignSyntheticOpaque_931_ = lean_ctor_get_uint8(v___x_923_, 7);
v_offsetCnstrs_932_ = lean_ctor_get_uint8(v___x_923_, 8);
v_etaStruct_933_ = lean_ctor_get_uint8(v___x_923_, 10);
v_univApprox_934_ = lean_ctor_get_uint8(v___x_923_, 11);
v_iota_935_ = lean_ctor_get_uint8(v___x_923_, 12);
v_beta_936_ = lean_ctor_get_uint8(v___x_923_, 13);
v_proj_937_ = lean_ctor_get_uint8(v___x_923_, 14);
v_zeta_938_ = lean_ctor_get_uint8(v___x_923_, 15);
v_zetaDelta_939_ = lean_ctor_get_uint8(v___x_923_, 16);
v_zetaUnused_940_ = lean_ctor_get_uint8(v___x_923_, 17);
v_zetaHave_941_ = lean_ctor_get_uint8(v___x_923_, 18);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_979_ == 0)
{
v___x_943_ = v___x_923_;
v_isShared_944_ = v_isSharedCheck_979_;
goto v_resetjp_942_;
}
else
{
lean_dec(v___x_923_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_979_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
uint8_t v_trackZetaDelta_945_; lean_object* v_zetaDeltaSet_946_; lean_object* v_lctx_947_; lean_object* v_localInstances_948_; lean_object* v_defEqCtx_x3f_949_; lean_object* v_synthPendingDepth_950_; lean_object* v_canUnfold_x3f_951_; uint8_t v_univApprox_952_; uint8_t v_inTypeClassResolution_953_; uint8_t v_cacheInferType_954_; lean_object* v_config_956_; 
v_trackZetaDelta_945_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_946_ = lean_ctor_get(v___y_683_, 1);
v_lctx_947_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_948_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_949_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_950_ = lean_ctor_get(v___y_683_, 5);
v_canUnfold_x3f_951_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_952_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_953_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_954_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
if (v_isShared_944_ == 0)
{
v_config_956_ = v___x_943_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 0, v_foApprox_924_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 1, v_ctxApprox_925_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 2, v_quasiPatternApprox_926_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 3, v_constApprox_927_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 4, v_isDefEqStuckEx_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 5, v_unificationHints_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 6, v_proofIrrelevance_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 7, v_assignSyntheticOpaque_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 8, v_offsetCnstrs_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 10, v_etaStruct_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 11, v_univApprox_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 12, v_iota_935_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 13, v_beta_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 14, v_proj_937_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 15, v_zeta_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 16, v_zetaDelta_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 17, v_zetaUnused_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 18, v_zetaHave_941_);
v_config_956_ = v_reuseFailAlloc_978_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
uint64_t v___x_957_; uint64_t v___x_958_; uint64_t v___x_959_; uint64_t v___x_960_; uint64_t v___x_961_; uint64_t v_key_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_ctor_set_uint8(v_config_956_, 9, v_transparency_674_);
v___x_957_ = l_Lean_Meta_Context_configKey(v___y_683_);
v___x_958_ = 3ULL;
v___x_959_ = lean_uint64_shift_right(v___x_957_, v___x_958_);
v___x_960_ = lean_uint64_shift_left(v___x_959_, v___x_958_);
v___x_961_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_674_);
v_key_962_ = lean_uint64_lor(v___x_960_, v___x_961_);
v___x_963_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_963_, 0, v_config_956_);
lean_ctor_set_uint64(v___x_963_, sizeof(void*)*1, v_key_962_);
lean_inc(v_canUnfold_x3f_951_);
lean_inc(v_synthPendingDepth_950_);
lean_inc(v_defEqCtx_x3f_949_);
lean_inc_ref(v_localInstances_948_);
lean_inc_ref(v_lctx_947_);
lean_inc(v_zetaDeltaSet_946_);
v___x_964_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v_zetaDeltaSet_946_);
lean_ctor_set(v___x_964_, 2, v_lctx_947_);
lean_ctor_set(v___x_964_, 3, v_localInstances_948_);
lean_ctor_set(v___x_964_, 4, v_defEqCtx_x3f_949_);
lean_ctor_set(v___x_964_, 5, v_synthPendingDepth_950_);
lean_ctor_set(v___x_964_, 6, v_canUnfold_x3f_951_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*7, v_trackZetaDelta_945_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*7 + 1, v_univApprox_952_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*7 + 2, v_inTypeClassResolution_953_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*7 + 3, v_cacheInferType_954_);
v___x_965_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_964_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_964_, 7);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = lean_box(0);
v___x_968_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_922_, v_hasTrace_689_, v_a_966_, v___x_967_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_977_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_977_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = l_List_reverse___redArg(v_a_969_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_973_);
v___x_975_ = v___x_971_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
return v___x_968_;
}
}
else
{
return v___x_965_;
}
}
}
}
else
{
goto v___jp_814_;
}
}
else
{
goto v___jp_814_;
}
v___jp_751_:
{
lean_object* v___x_755_; double v___x_756_; double v___x_757_; double v___x_758_; double v___x_759_; double v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_755_ = lean_io_mono_nanos_now();
v___x_756_ = lean_float_of_nat(v___y_753_);
v___x_757_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_758_ = lean_float_div(v___x_756_, v___x_757_);
v___x_759_ = lean_float_of_nat(v___x_755_);
v___x_760_ = lean_float_div(v___x_759_, v___x_757_);
v___x_761_ = lean_box_float(v___x_758_);
v___x_762_ = lean_box_float(v___x_760_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_a_754_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_679_, v___x_680_, v___x_681_, v_options_688_, v___x_750_, v___y_752_, v___f_682_, v___x_764_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_765_;
}
v___jp_766_:
{
lean_object* v___x_770_; 
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v_a_769_);
v___y_752_ = v___y_768_;
v___y_753_ = v___y_767_;
v_a_754_ = v___x_770_;
goto v___jp_751_;
}
v___jp_771_:
{
if (lean_obj_tag(v___y_774_) == 0)
{
lean_object* v_a_775_; 
v_a_775_ = lean_ctor_get(v___y_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___y_774_, 1);
v___y_767_ = v___y_773_;
v___y_768_ = v___y_772_;
v_a_769_ = v_a_775_;
goto v___jp_766_;
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v_a_776_ = lean_ctor_get(v___y_774_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___y_774_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___y_774_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___y_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set_tag(v___x_778_, 0);
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
v___y_752_ = v___y_772_;
v___y_753_ = v___y_773_;
v_a_754_ = v___x_781_;
goto v___jp_751_;
}
}
}
}
v___jp_784_:
{
lean_object* v___x_788_; double v___x_789_; double v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_788_ = lean_io_get_num_heartbeats();
v___x_789_ = lean_float_of_nat(v___y_785_);
v___x_790_ = lean_float_of_nat(v___x_788_);
v___x_791_ = lean_box_float(v___x_789_);
v___x_792_ = lean_box_float(v___x_790_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v_a_787_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_679_, v___x_680_, v___x_681_, v_options_688_, v___x_750_, v___y_786_, v___f_682_, v___x_794_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_795_;
}
v___jp_796_:
{
lean_object* v___x_800_; 
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v_a_799_);
v___y_785_ = v___y_797_;
v___y_786_ = v___y_798_;
v_a_787_ = v___x_800_;
goto v___jp_784_;
}
v___jp_801_:
{
if (lean_obj_tag(v___y_804_) == 0)
{
lean_object* v_a_805_; 
v_a_805_ = lean_ctor_get(v___y_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___y_804_, 1);
v___y_797_ = v___y_802_;
v___y_798_ = v___y_803_;
v_a_799_ = v_a_805_;
goto v___jp_796_;
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
v_a_806_ = lean_ctor_get(v___y_804_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___y_804_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___y_804_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___y_804_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 0);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
v___y_785_ = v___y_802_;
v___y_786_ = v___y_803_;
v_a_787_ = v___x_811_;
goto v___jp_784_;
}
}
}
}
v___jp_814_:
{
lean_object* v___x_815_; lean_object* v_a_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_815_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_686_);
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref(v___x_815_);
v___x_817_ = l_Lean_trace_profiler_useHeartbeats;
v___x_818_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_688_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v_foApprox_821_; uint8_t v_ctxApprox_822_; uint8_t v_quasiPatternApprox_823_; uint8_t v_constApprox_824_; uint8_t v_isDefEqStuckEx_825_; uint8_t v_unificationHints_826_; uint8_t v_proofIrrelevance_827_; uint8_t v_assignSyntheticOpaque_828_; uint8_t v_offsetCnstrs_829_; uint8_t v_etaStruct_830_; uint8_t v_univApprox_831_; uint8_t v_iota_832_; uint8_t v_beta_833_; uint8_t v_proj_834_; uint8_t v_zeta_835_; uint8_t v_zetaDelta_836_; uint8_t v_zetaUnused_837_; uint8_t v_zetaHave_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_869_; 
v___x_819_ = lean_io_mono_nanos_now();
v___x_820_ = l_Lean_Meta_Context_config(v___y_683_);
v_foApprox_821_ = lean_ctor_get_uint8(v___x_820_, 0);
v_ctxApprox_822_ = lean_ctor_get_uint8(v___x_820_, 1);
v_quasiPatternApprox_823_ = lean_ctor_get_uint8(v___x_820_, 2);
v_constApprox_824_ = lean_ctor_get_uint8(v___x_820_, 3);
v_isDefEqStuckEx_825_ = lean_ctor_get_uint8(v___x_820_, 4);
v_unificationHints_826_ = lean_ctor_get_uint8(v___x_820_, 5);
v_proofIrrelevance_827_ = lean_ctor_get_uint8(v___x_820_, 6);
v_assignSyntheticOpaque_828_ = lean_ctor_get_uint8(v___x_820_, 7);
v_offsetCnstrs_829_ = lean_ctor_get_uint8(v___x_820_, 8);
v_etaStruct_830_ = lean_ctor_get_uint8(v___x_820_, 10);
v_univApprox_831_ = lean_ctor_get_uint8(v___x_820_, 11);
v_iota_832_ = lean_ctor_get_uint8(v___x_820_, 12);
v_beta_833_ = lean_ctor_get_uint8(v___x_820_, 13);
v_proj_834_ = lean_ctor_get_uint8(v___x_820_, 14);
v_zeta_835_ = lean_ctor_get_uint8(v___x_820_, 15);
v_zetaDelta_836_ = lean_ctor_get_uint8(v___x_820_, 16);
v_zetaUnused_837_ = lean_ctor_get_uint8(v___x_820_, 17);
v_zetaHave_838_ = lean_ctor_get_uint8(v___x_820_, 18);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_869_ == 0)
{
v___x_840_ = v___x_820_;
v_isShared_841_ = v_isSharedCheck_869_;
goto v_resetjp_839_;
}
else
{
lean_dec(v___x_820_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_869_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
uint8_t v_trackZetaDelta_842_; lean_object* v_zetaDeltaSet_843_; lean_object* v_lctx_844_; lean_object* v_localInstances_845_; lean_object* v_defEqCtx_x3f_846_; lean_object* v_synthPendingDepth_847_; lean_object* v_canUnfold_x3f_848_; uint8_t v_univApprox_849_; uint8_t v_inTypeClassResolution_850_; uint8_t v_cacheInferType_851_; lean_object* v_config_853_; 
v_trackZetaDelta_842_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_843_ = lean_ctor_get(v___y_683_, 1);
v_lctx_844_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_845_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_846_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_847_ = lean_ctor_get(v___y_683_, 5);
v_canUnfold_x3f_848_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_849_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_850_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_851_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
if (v_isShared_841_ == 0)
{
v_config_853_ = v___x_840_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 0, v_foApprox_821_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 1, v_ctxApprox_822_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 2, v_quasiPatternApprox_823_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 3, v_constApprox_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 4, v_isDefEqStuckEx_825_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 5, v_unificationHints_826_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 6, v_proofIrrelevance_827_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 7, v_assignSyntheticOpaque_828_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 8, v_offsetCnstrs_829_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 10, v_etaStruct_830_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 11, v_univApprox_831_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 12, v_iota_832_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 13, v_beta_833_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 14, v_proj_834_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 15, v_zeta_835_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 16, v_zetaDelta_836_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 17, v_zetaUnused_837_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 18, v_zetaHave_838_);
v_config_853_ = v_reuseFailAlloc_868_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
uint64_t v___x_854_; uint64_t v___x_855_; uint64_t v___x_856_; uint64_t v___x_857_; uint64_t v___x_858_; uint64_t v_key_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
lean_ctor_set_uint8(v_config_853_, 9, v_transparency_674_);
v___x_854_ = l_Lean_Meta_Context_configKey(v___y_683_);
v___x_855_ = 3ULL;
v___x_856_ = lean_uint64_shift_right(v___x_854_, v___x_855_);
v___x_857_ = lean_uint64_shift_left(v___x_856_, v___x_855_);
v___x_858_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_674_);
v_key_859_ = lean_uint64_lor(v___x_857_, v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_860_, 0, v_config_853_);
lean_ctor_set_uint64(v___x_860_, sizeof(void*)*1, v_key_859_);
lean_inc(v_canUnfold_x3f_848_);
lean_inc(v_synthPendingDepth_847_);
lean_inc(v_defEqCtx_x3f_846_);
lean_inc_ref(v_localInstances_845_);
lean_inc_ref(v_lctx_844_);
lean_inc(v_zetaDeltaSet_843_);
v___x_861_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v_zetaDeltaSet_843_);
lean_ctor_set(v___x_861_, 2, v_lctx_844_);
lean_ctor_set(v___x_861_, 3, v_localInstances_845_);
lean_ctor_set(v___x_861_, 4, v_defEqCtx_x3f_846_);
lean_ctor_set(v___x_861_, 5, v_synthPendingDepth_847_);
lean_ctor_set(v___x_861_, 6, v_canUnfold_x3f_848_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*7, v_trackZetaDelta_842_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*7 + 1, v_univApprox_849_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*7 + 2, v_inTypeClassResolution_850_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*7 + 3, v_cacheInferType_851_);
v___x_862_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_861_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_861_, 7);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = lean_box(0);
v___x_865_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_818_, v_hasTrace_689_, v_a_863_, v___x_864_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_867_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_865_, 1);
v___x_867_ = l_List_reverse___redArg(v_a_866_);
v___y_767_ = v___x_819_;
v___y_768_ = v_a_816_;
v_a_769_ = v___x_867_;
goto v___jp_766_;
}
else
{
v___y_772_ = v_a_816_;
v___y_773_ = v___x_819_;
v___y_774_ = v___x_865_;
goto v___jp_771_;
}
}
else
{
v___y_772_ = v_a_816_;
v___y_773_ = v___x_819_;
v___y_774_ = v___x_862_;
goto v___jp_771_;
}
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v_foApprox_872_; uint8_t v_ctxApprox_873_; uint8_t v_quasiPatternApprox_874_; uint8_t v_constApprox_875_; uint8_t v_isDefEqStuckEx_876_; uint8_t v_unificationHints_877_; uint8_t v_proofIrrelevance_878_; uint8_t v_assignSyntheticOpaque_879_; uint8_t v_offsetCnstrs_880_; uint8_t v_etaStruct_881_; uint8_t v_univApprox_882_; uint8_t v_iota_883_; uint8_t v_beta_884_; uint8_t v_proj_885_; uint8_t v_zeta_886_; uint8_t v_zetaDelta_887_; uint8_t v_zetaUnused_888_; uint8_t v_zetaHave_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_920_; 
v___x_870_ = lean_io_get_num_heartbeats();
v___x_871_ = l_Lean_Meta_Context_config(v___y_683_);
v_foApprox_872_ = lean_ctor_get_uint8(v___x_871_, 0);
v_ctxApprox_873_ = lean_ctor_get_uint8(v___x_871_, 1);
v_quasiPatternApprox_874_ = lean_ctor_get_uint8(v___x_871_, 2);
v_constApprox_875_ = lean_ctor_get_uint8(v___x_871_, 3);
v_isDefEqStuckEx_876_ = lean_ctor_get_uint8(v___x_871_, 4);
v_unificationHints_877_ = lean_ctor_get_uint8(v___x_871_, 5);
v_proofIrrelevance_878_ = lean_ctor_get_uint8(v___x_871_, 6);
v_assignSyntheticOpaque_879_ = lean_ctor_get_uint8(v___x_871_, 7);
v_offsetCnstrs_880_ = lean_ctor_get_uint8(v___x_871_, 8);
v_etaStruct_881_ = lean_ctor_get_uint8(v___x_871_, 10);
v_univApprox_882_ = lean_ctor_get_uint8(v___x_871_, 11);
v_iota_883_ = lean_ctor_get_uint8(v___x_871_, 12);
v_beta_884_ = lean_ctor_get_uint8(v___x_871_, 13);
v_proj_885_ = lean_ctor_get_uint8(v___x_871_, 14);
v_zeta_886_ = lean_ctor_get_uint8(v___x_871_, 15);
v_zetaDelta_887_ = lean_ctor_get_uint8(v___x_871_, 16);
v_zetaUnused_888_ = lean_ctor_get_uint8(v___x_871_, 17);
v_zetaHave_889_ = lean_ctor_get_uint8(v___x_871_, 18);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_920_ == 0)
{
v___x_891_ = v___x_871_;
v_isShared_892_ = v_isSharedCheck_920_;
goto v_resetjp_890_;
}
else
{
lean_dec(v___x_871_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_920_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
uint8_t v_trackZetaDelta_893_; lean_object* v_zetaDeltaSet_894_; lean_object* v_lctx_895_; lean_object* v_localInstances_896_; lean_object* v_defEqCtx_x3f_897_; lean_object* v_synthPendingDepth_898_; lean_object* v_canUnfold_x3f_899_; uint8_t v_univApprox_900_; uint8_t v_inTypeClassResolution_901_; uint8_t v_cacheInferType_902_; lean_object* v_config_904_; 
v_trackZetaDelta_893_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_894_ = lean_ctor_get(v___y_683_, 1);
v_lctx_895_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_896_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_897_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_898_ = lean_ctor_get(v___y_683_, 5);
v_canUnfold_x3f_899_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_900_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_901_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_902_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
if (v_isShared_892_ == 0)
{
v_config_904_ = v___x_891_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 0, v_foApprox_872_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 1, v_ctxApprox_873_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 2, v_quasiPatternApprox_874_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 3, v_constApprox_875_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 4, v_isDefEqStuckEx_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 5, v_unificationHints_877_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 6, v_proofIrrelevance_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 7, v_assignSyntheticOpaque_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 8, v_offsetCnstrs_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 10, v_etaStruct_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 11, v_univApprox_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 12, v_iota_883_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 13, v_beta_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 14, v_proj_885_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 15, v_zeta_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 16, v_zetaDelta_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 17, v_zetaUnused_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 18, v_zetaHave_889_);
v_config_904_ = v_reuseFailAlloc_919_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
uint64_t v___x_905_; uint64_t v___x_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v_key_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_ctor_set_uint8(v_config_904_, 9, v_transparency_674_);
v___x_905_ = l_Lean_Meta_Context_configKey(v___y_683_);
v___x_906_ = 3ULL;
v___x_907_ = lean_uint64_shift_right(v___x_905_, v___x_906_);
v___x_908_ = lean_uint64_shift_left(v___x_907_, v___x_906_);
v___x_909_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_674_);
v_key_910_ = lean_uint64_lor(v___x_908_, v___x_909_);
v___x_911_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_911_, 0, v_config_904_);
lean_ctor_set_uint64(v___x_911_, sizeof(void*)*1, v_key_910_);
lean_inc(v_canUnfold_x3f_899_);
lean_inc(v_synthPendingDepth_898_);
lean_inc(v_defEqCtx_x3f_897_);
lean_inc_ref(v_localInstances_896_);
lean_inc_ref(v_lctx_895_);
lean_inc(v_zetaDeltaSet_894_);
v___x_912_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_zetaDeltaSet_894_);
lean_ctor_set(v___x_912_, 2, v_lctx_895_);
lean_ctor_set(v___x_912_, 3, v_localInstances_896_);
lean_ctor_set(v___x_912_, 4, v_defEqCtx_x3f_897_);
lean_ctor_set(v___x_912_, 5, v_synthPendingDepth_898_);
lean_ctor_set(v___x_912_, 6, v_canUnfold_x3f_899_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*7, v_trackZetaDelta_893_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*7 + 1, v_univApprox_900_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*7 + 2, v_inTypeClassResolution_901_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*7 + 3, v_cacheInferType_902_);
v___x_913_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_912_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_912_, 7);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = lean_box(0);
v___x_916_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_818_, v_a_914_, v___x_915_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = l_List_reverse___redArg(v_a_917_);
v___y_797_ = v___x_870_;
v___y_798_ = v_a_816_;
v_a_799_ = v___x_918_;
goto v___jp_796_;
}
else
{
v___y_802_ = v___x_870_;
v___y_803_ = v_a_816_;
v___y_804_ = v___x_916_;
goto v___jp_801_;
}
}
else
{
v___y_802_ = v___x_870_;
v___y_803_ = v_a_816_;
v___y_804_ = v___x_913_;
goto v___jp_801_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_980_, lean_object* v_g_981_, lean_object* v_e_982_, lean_object* v_cfg_983_, lean_object* v___x_984_, lean_object* v___x_985_, lean_object* v___x_986_, lean_object* v___x_987_, lean_object* v___f_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
uint8_t v_transparency_boxed_994_; uint8_t v___x_14741__boxed_995_; lean_object* v_res_996_; 
v_transparency_boxed_994_ = lean_unbox(v_transparency_980_);
v___x_14741__boxed_995_ = lean_unbox(v___x_986_);
v_res_996_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_994_, v_g_981_, v_e_982_, v_cfg_983_, v___x_984_, v___x_985_, v___x_14741__boxed_995_, v___x_987_, v___f_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_998_, lean_object* v_g_999_, lean_object* v_cfg_1000_, lean_object* v_e_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___f_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___f_1014_; lean_object* v___x_1015_; 
lean_inc_ref(v_e_1001_);
v___f_1007_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1007_, 0, v_e_1001_);
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_1009_ = lean_box(0);
v___x_1010_ = 1;
v___x_1011_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_1012_ = lean_box(v_transparency_998_);
v___x_1013_ = lean_box(v___x_1010_);
v___f_1014_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_1014_, 0, v___x_1012_);
lean_closure_set(v___f_1014_, 1, v_g_999_);
lean_closure_set(v___f_1014_, 2, v_e_1001_);
lean_closure_set(v___f_1014_, 3, v_cfg_1000_);
lean_closure_set(v___f_1014_, 4, v___x_1009_);
lean_closure_set(v___f_1014_, 5, v___x_1008_);
lean_closure_set(v___f_1014_, 6, v___x_1013_);
lean_closure_set(v___f_1014_, 7, v___x_1011_);
lean_closure_set(v___f_1014_, 8, v___f_1007_);
v___x_1015_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_1014_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_1016_, lean_object* v_g_1017_, lean_object* v_cfg_1018_, lean_object* v_e_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
uint8_t v_transparency_boxed_1025_; lean_object* v_res_1026_; 
v_transparency_boxed_1025_ = lean_unbox(v_transparency_1016_);
v_res_1026_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_1025_, v_g_1017_, v_cfg_1018_, v_e_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_1027_, uint8_t v_transparency_1028_, lean_object* v_lemmas_1029_, lean_object* v_g_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_1029_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1045_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___f_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1039_ = lean_box(v_transparency_1028_);
v___f_1040_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1040_, 0, v___x_1039_);
lean_closure_set(v___f_1040_, 1, v_g_1030_);
lean_closure_set(v___f_1040_, 2, v_cfg_1027_);
v___x_1041_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_1041_, 0, lean_box(0));
lean_closure_set(v___x_1041_, 1, lean_box(0));
lean_closure_set(v___x_1041_, 2, v___f_1040_);
lean_closure_set(v___x_1041_, 3, v_a_1035_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1041_);
v___x_1043_ = v___x_1037_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec(v_g_1030_);
lean_dec_ref(v_cfg_1027_);
v_a_1046_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1034_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1034_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_1054_, lean_object* v_transparency_1055_, lean_object* v_lemmas_1056_, lean_object* v_g_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
uint8_t v_transparency_boxed_1061_; lean_object* v_res_1062_; 
v_transparency_boxed_1061_ = lean_unbox(v_transparency_1055_);
v_res_1062_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1054_, v_transparency_boxed_1061_, v_lemmas_1056_, v_g_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec(v_a_1058_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_1063_, uint8_t v_transparency_1064_, lean_object* v_lemmas_1065_, lean_object* v_g_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1063_, v_transparency_1064_, v_lemmas_1065_, v_g_1066_, v_a_1068_, v_a_1070_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_1073_, lean_object* v_transparency_1074_, lean_object* v_lemmas_1075_, lean_object* v_g_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
uint8_t v_transparency_boxed_1082_; lean_object* v_res_1083_; 
v_transparency_boxed_1082_ = lean_unbox(v_transparency_1074_);
v_res_1083_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_1073_, v_transparency_boxed_1082_, v_lemmas_1075_, v_g_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_00_u03b1_1084_, lean_object* v_x_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_1085_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_00_u03b1_1092_, v_x_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1100_, uint8_t v_transparency_1101_, lean_object* v_lemmas_1102_, lean_object* v_g_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1100_, v_transparency_1101_, v_lemmas_1102_, v_g_1103_, v_a_1105_, v_a_1107_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1111_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = l_Lean_Meta_Iterator_head___redArg(v_a_1110_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1111_;
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
v_a_1112_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1109_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1109_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1120_, lean_object* v_transparency_1121_, lean_object* v_lemmas_1122_, lean_object* v_g_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
uint8_t v_transparency_boxed_1129_; lean_object* v_res_1130_; 
v_transparency_boxed_1129_ = lean_unbox(v_transparency_1121_);
v_res_1130_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1120_, v_transparency_boxed_1129_, v_lemmas_1122_, v_g_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1131_){
_start:
{
lean_object* v_toApplyRulesConfig_1132_; lean_object* v_toBacktrackConfig_1133_; 
v_toApplyRulesConfig_1132_ = lean_ctor_get(v_x_1131_, 0);
v_toBacktrackConfig_1133_ = lean_ctor_get(v_toApplyRulesConfig_1132_, 0);
lean_inc_ref(v_toBacktrackConfig_1133_);
return v_toBacktrackConfig_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1134_);
lean_dec_ref(v_x_1134_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1138_, lean_object* v_discharge_1139_, lean_object* v_g_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
lean_inc(v_g_1140_);
v___x_1146_ = lean_apply_6(v_test_1138_, v_g_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, lean_box(0));
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1157_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1157_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1157_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
uint8_t v___x_1151_; 
v___x_1151_ = lean_unbox(v_a_1147_);
lean_dec(v_a_1147_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
lean_del_object(v___x_1149_);
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
v___x_1152_ = lean_apply_6(v_discharge_1139_, v_g_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, lean_box(0));
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
lean_dec(v_g_1140_);
lean_dec_ref(v_discharge_1139_);
v___x_1153_ = lean_box(0);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1153_);
v___x_1155_ = v___x_1149_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_g_1140_);
lean_dec_ref(v_discharge_1139_);
v_a_1158_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1146_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1146_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1166_, lean_object* v_discharge_1167_, lean_object* v_g_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1166_, v_discharge_1167_, v_g_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1175_, lean_object* v_test_1176_){
_start:
{
lean_object* v_toApplyRulesConfig_1177_; lean_object* v_toBacktrackConfig_1178_; uint8_t v_backtracking_1179_; uint8_t v_intro_1180_; uint8_t v_constructor_1181_; uint8_t v_suggestions_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1214_; 
v_toApplyRulesConfig_1177_ = lean_ctor_get(v_cfg_1175_, 0);
lean_inc_ref(v_toApplyRulesConfig_1177_);
v_toBacktrackConfig_1178_ = lean_ctor_get(v_toApplyRulesConfig_1177_, 0);
lean_inc_ref(v_toBacktrackConfig_1178_);
v_backtracking_1179_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*1);
v_intro_1180_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*1 + 1);
v_constructor_1181_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*1 + 2);
v_suggestions_1182_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*1 + 3);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_cfg_1175_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; 
v_unused_1215_ = lean_ctor_get(v_cfg_1175_, 0);
lean_dec(v_unused_1215_);
v___x_1184_ = v_cfg_1175_;
v_isShared_1185_ = v_isSharedCheck_1214_;
goto v_resetjp_1183_;
}
else
{
lean_dec(v_cfg_1175_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1214_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v_toApplyConfig_1186_; uint8_t v_transparency_1187_; uint8_t v_symm_1188_; uint8_t v_exfalso_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1212_; 
v_toApplyConfig_1186_ = lean_ctor_get(v_toApplyRulesConfig_1177_, 1);
v_transparency_1187_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1177_, sizeof(void*)*2);
v_symm_1188_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1177_, sizeof(void*)*2 + 1);
v_exfalso_1189_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1177_, sizeof(void*)*2 + 2);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_toApplyRulesConfig_1177_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v_toApplyRulesConfig_1177_, 0);
lean_dec(v_unused_1213_);
v___x_1191_ = v_toApplyRulesConfig_1177_;
v_isShared_1192_ = v_isSharedCheck_1212_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_toApplyConfig_1186_);
lean_dec(v_toApplyRulesConfig_1177_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1212_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v_maxDepth_1193_; lean_object* v_proc_1194_; lean_object* v_suspend_1195_; lean_object* v_discharge_1196_; uint8_t v_commitIndependentGoals_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1211_; 
v_maxDepth_1193_ = lean_ctor_get(v_toBacktrackConfig_1178_, 0);
v_proc_1194_ = lean_ctor_get(v_toBacktrackConfig_1178_, 1);
v_suspend_1195_ = lean_ctor_get(v_toBacktrackConfig_1178_, 2);
v_discharge_1196_ = lean_ctor_get(v_toBacktrackConfig_1178_, 3);
v_commitIndependentGoals_1197_ = lean_ctor_get_uint8(v_toBacktrackConfig_1178_, sizeof(void*)*4);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_toBacktrackConfig_1178_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1199_ = v_toBacktrackConfig_1178_;
v_isShared_1200_ = v_isSharedCheck_1211_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_discharge_1196_);
lean_inc(v_suspend_1195_);
lean_inc(v_proc_1194_);
lean_inc(v_maxDepth_1193_);
lean_dec(v_toBacktrackConfig_1178_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1211_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___f_1201_; lean_object* v___x_1203_; 
v___f_1201_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1201_, 0, v_test_1176_);
lean_closure_set(v___f_1201_, 1, v_discharge_1196_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 3, v___f_1201_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_maxDepth_1193_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_proc_1194_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_suspend_1195_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v___f_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*4, v_commitIndependentGoals_1197_);
v___x_1203_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1203_);
v___x_1205_ = v___x_1191_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_toApplyConfig_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*2, v_transparency_1187_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*2 + 1, v_symm_1188_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*2 + 2, v_exfalso_1189_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1205_);
v___x_1207_ = v___x_1184_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*1, v_backtracking_1179_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*1 + 1, v_intro_1180_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*1 + 2, v_constructor_1181_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*1 + 3, v_suggestions_1182_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1216_, lean_object* v_proc_1217_, lean_object* v_orig_1218_, lean_object* v_goals_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
if (lean_obj_tag(v_goals_1219_) == 0)
{
lean_object* v___x_1225_; 
lean_dec_ref(v_proc_1217_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
v___x_1225_ = lean_apply_7(v_proc_1216_, v_orig_1218_, v_goals_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, lean_box(0));
return v___x_1225_;
}
else
{
lean_object* v_head_1226_; lean_object* v_tail_1227_; lean_object* v___x_1228_; 
v_head_1226_ = lean_ctor_get(v_goals_1219_, 0);
v_tail_1227_ = lean_ctor_get(v_goals_1219_, 1);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
lean_inc(v_head_1226_);
v___x_1228_ = lean_apply_6(v_proc_1217_, v_head_1226_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, lean_box(0));
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1238_; 
lean_inc(v_tail_1227_);
lean_dec_ref_known(v_goals_1219_, 2);
lean_dec(v_orig_1218_);
lean_dec_ref(v_proc_1216_);
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1238_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1238_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1233_ = l_List_appendTR___redArg(v_a_1229_, v_tail_1227_);
v___x_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1234_);
v___x_1236_ = v___x_1231_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1251_; 
v_a_1239_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1241_ = v___x_1228_;
v_isShared_1242_ = v_isSharedCheck_1251_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1228_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1251_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
uint8_t v___y_1244_; uint8_t v___x_1249_; 
v___x_1249_ = l_Lean_Exception_isInterrupt(v_a_1239_);
if (v___x_1249_ == 0)
{
uint8_t v___x_1250_; 
lean_inc(v_a_1239_);
v___x_1250_ = l_Lean_Exception_isRuntime(v_a_1239_);
v___y_1244_ = v___x_1250_;
goto v___jp_1243_;
}
else
{
v___y_1244_ = v___x_1249_;
goto v___jp_1243_;
}
v___jp_1243_:
{
if (v___y_1244_ == 0)
{
lean_object* v___x_1245_; 
lean_del_object(v___x_1241_);
lean_dec(v_a_1239_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
v___x_1245_ = lean_apply_7(v_proc_1216_, v_orig_1218_, v_goals_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, lean_box(0));
return v___x_1245_;
}
else
{
lean_object* v___x_1247_; 
lean_dec_ref_known(v_goals_1219_, 2);
lean_dec(v_orig_1218_);
lean_dec_ref(v_proc_1216_);
if (v_isShared_1242_ == 0)
{
v___x_1247_ = v___x_1241_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1239_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1252_, lean_object* v_proc_1253_, lean_object* v_orig_1254_, lean_object* v_goals_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1252_, v_proc_1253_, v_orig_1254_, v_goals_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1262_, lean_object* v_proc_1263_){
_start:
{
lean_object* v_toApplyRulesConfig_1264_; lean_object* v_toBacktrackConfig_1265_; uint8_t v_backtracking_1266_; uint8_t v_intro_1267_; uint8_t v_constructor_1268_; uint8_t v_suggestions_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1301_; 
v_toApplyRulesConfig_1264_ = lean_ctor_get(v_cfg_1262_, 0);
lean_inc_ref(v_toApplyRulesConfig_1264_);
v_toBacktrackConfig_1265_ = lean_ctor_get(v_toApplyRulesConfig_1264_, 0);
lean_inc_ref(v_toBacktrackConfig_1265_);
v_backtracking_1266_ = lean_ctor_get_uint8(v_cfg_1262_, sizeof(void*)*1);
v_intro_1267_ = lean_ctor_get_uint8(v_cfg_1262_, sizeof(void*)*1 + 1);
v_constructor_1268_ = lean_ctor_get_uint8(v_cfg_1262_, sizeof(void*)*1 + 2);
v_suggestions_1269_ = lean_ctor_get_uint8(v_cfg_1262_, sizeof(void*)*1 + 3);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_cfg_1262_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v_cfg_1262_, 0);
lean_dec(v_unused_1302_);
v___x_1271_ = v_cfg_1262_;
v_isShared_1272_ = v_isSharedCheck_1301_;
goto v_resetjp_1270_;
}
else
{
lean_dec(v_cfg_1262_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1301_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v_toApplyConfig_1273_; uint8_t v_transparency_1274_; uint8_t v_symm_1275_; uint8_t v_exfalso_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1299_; 
v_toApplyConfig_1273_ = lean_ctor_get(v_toApplyRulesConfig_1264_, 1);
v_transparency_1274_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1264_, sizeof(void*)*2);
v_symm_1275_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1264_, sizeof(void*)*2 + 1);
v_exfalso_1276_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1264_, sizeof(void*)*2 + 2);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_toApplyRulesConfig_1264_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v_toApplyRulesConfig_1264_, 0);
lean_dec(v_unused_1300_);
v___x_1278_ = v_toApplyRulesConfig_1264_;
v_isShared_1279_ = v_isSharedCheck_1299_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_toApplyConfig_1273_);
lean_dec(v_toApplyRulesConfig_1264_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1299_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_maxDepth_1280_; lean_object* v_proc_1281_; lean_object* v_suspend_1282_; lean_object* v_discharge_1283_; uint8_t v_commitIndependentGoals_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1298_; 
v_maxDepth_1280_ = lean_ctor_get(v_toBacktrackConfig_1265_, 0);
v_proc_1281_ = lean_ctor_get(v_toBacktrackConfig_1265_, 1);
v_suspend_1282_ = lean_ctor_get(v_toBacktrackConfig_1265_, 2);
v_discharge_1283_ = lean_ctor_get(v_toBacktrackConfig_1265_, 3);
v_commitIndependentGoals_1284_ = lean_ctor_get_uint8(v_toBacktrackConfig_1265_, sizeof(void*)*4);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_toBacktrackConfig_1265_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1286_ = v_toBacktrackConfig_1265_;
v_isShared_1287_ = v_isSharedCheck_1298_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_discharge_1283_);
lean_inc(v_suspend_1282_);
lean_inc(v_proc_1281_);
lean_inc(v_maxDepth_1280_);
lean_dec(v_toBacktrackConfig_1265_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1298_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___f_1288_; lean_object* v___x_1290_; 
v___f_1288_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1288_, 0, v_proc_1281_);
lean_closure_set(v___f_1288_, 1, v_proc_1263_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v___f_1288_);
v___x_1290_ = v___x_1286_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_maxDepth_1280_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v___f_1288_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_suspend_1282_);
lean_ctor_set(v_reuseFailAlloc_1297_, 3, v_discharge_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*4, v_commitIndependentGoals_1284_);
v___x_1290_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1292_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1290_);
v___x_1292_ = v___x_1278_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_toApplyConfig_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*2, v_transparency_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*2 + 1, v_symm_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*2 + 2, v_exfalso_1276_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1294_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1292_);
v___x_1294_ = v___x_1271_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*1, v_backtracking_1266_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*1 + 1, v_intro_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*1 + 2, v_constructor_1268_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*1 + 3, v_suggestions_1269_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
uint8_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = 1;
v___x_1310_ = l_Lean_Meta_intro1Core(v_g_1303_, v___x_1309_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1328_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1328_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1328_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_snd_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1326_; 
v_snd_1315_ = lean_ctor_get(v_a_1311_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_a_1311_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v_a_1311_, 0);
lean_dec(v_unused_1327_);
v___x_1317_ = v_a_1311_;
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_snd_1315_);
lean_dec(v_a_1311_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_box(0);
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 1);
lean_ctor_set(v___x_1317_, 1, v___x_1319_);
lean_ctor_set(v___x_1317_, 0, v_snd_1315_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_snd_1315_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1323_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1321_);
v___x_1323_ = v___x_1313_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1310_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1310_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1345_){
_start:
{
lean_object* v___f_1346_; lean_object* v___x_1347_; 
v___f_1346_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1347_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1345_, v___f_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
lean_object* v_ks_1352_; lean_object* v_vs_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1377_; 
v_ks_1352_ = lean_ctor_get(v_x_1348_, 0);
v_vs_1353_ = lean_ctor_get(v_x_1348_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1355_ = v_x_1348_;
v_isShared_1356_ = v_isSharedCheck_1377_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_vs_1353_);
lean_inc(v_ks_1352_);
lean_dec(v_x_1348_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1377_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = lean_array_get_size(v_ks_1352_);
v___x_1358_ = lean_nat_dec_lt(v_x_1349_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
lean_dec(v_x_1349_);
v___x_1359_ = lean_array_push(v_ks_1352_, v_x_1350_);
v___x_1360_ = lean_array_push(v_vs_1353_, v_x_1351_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1360_);
lean_ctor_set(v___x_1355_, 0, v___x_1359_);
v___x_1362_ = v___x_1355_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
else
{
lean_object* v_k_x27_1364_; uint8_t v___x_1365_; 
v_k_x27_1364_ = lean_array_fget_borrowed(v_ks_1352_, v_x_1349_);
v___x_1365_ = l_Lean_instBEqMVarId_beq(v_x_1350_, v_k_x27_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1367_; 
if (v_isShared_1356_ == 0)
{
v___x_1367_ = v___x_1355_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_ks_1352_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_vs_1353_);
v___x_1367_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_nat_add(v_x_1349_, v___x_1368_);
lean_dec(v_x_1349_);
v_x_1348_ = v___x_1367_;
v_x_1349_ = v___x_1369_;
goto _start;
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1372_ = lean_array_fset(v_ks_1352_, v_x_1349_, v_x_1350_);
v___x_1373_ = lean_array_fset(v_vs_1353_, v_x_1349_, v_x_1351_);
lean_dec(v_x_1349_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1373_);
lean_ctor_set(v___x_1355_, 0, v___x_1372_);
v___x_1375_ = v___x_1355_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1378_, lean_object* v_k_1379_, lean_object* v_v_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1378_, v___x_1381_, v_k_1379_, v_v_1380_);
return v___x_1382_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; 
v___x_1383_ = ((size_t)5ULL);
v___x_1384_ = ((size_t)1ULL);
v___x_1385_ = lean_usize_shift_left(v___x_1384_, v___x_1383_);
return v___x_1385_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1386_; size_t v___x_1387_; size_t v___x_1388_; 
v___x_1386_ = ((size_t)1ULL);
v___x_1387_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1388_ = lean_usize_sub(v___x_1387_, v___x_1386_);
return v___x_1388_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1390_, size_t v_x_1391_, size_t v_x_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_){
_start:
{
if (lean_obj_tag(v_x_1390_) == 0)
{
lean_object* v_es_1395_; size_t v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; lean_object* v_j_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_es_1395_ = lean_ctor_get(v_x_1390_, 0);
v___x_1396_ = ((size_t)5ULL);
v___x_1397_ = ((size_t)1ULL);
v___x_1398_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1399_ = lean_usize_land(v_x_1391_, v___x_1398_);
v_j_1400_ = lean_usize_to_nat(v___x_1399_);
v___x_1401_ = lean_array_get_size(v_es_1395_);
v___x_1402_ = lean_nat_dec_lt(v_j_1400_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_dec(v_j_1400_);
lean_dec(v_x_1394_);
lean_dec(v_x_1393_);
return v_x_1390_;
}
else
{
lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1439_; 
lean_inc_ref(v_es_1395_);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v_x_1390_, 0);
lean_dec(v_unused_1440_);
v___x_1404_ = v_x_1390_;
v_isShared_1405_ = v_isSharedCheck_1439_;
goto v_resetjp_1403_;
}
else
{
lean_dec(v_x_1390_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1439_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_v_1406_; lean_object* v___x_1407_; lean_object* v_xs_x27_1408_; lean_object* v___y_1410_; 
v_v_1406_ = lean_array_fget(v_es_1395_, v_j_1400_);
v___x_1407_ = lean_box(0);
v_xs_x27_1408_ = lean_array_fset(v_es_1395_, v_j_1400_, v___x_1407_);
switch(lean_obj_tag(v_v_1406_))
{
case 0:
{
lean_object* v_key_1415_; lean_object* v_val_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1426_; 
v_key_1415_ = lean_ctor_get(v_v_1406_, 0);
v_val_1416_ = lean_ctor_get(v_v_1406_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_v_1406_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1418_ = v_v_1406_;
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_val_1416_);
lean_inc(v_key_1415_);
lean_dec(v_v_1406_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
uint8_t v___x_1420_; 
v___x_1420_ = l_Lean_instBEqMVarId_beq(v_x_1393_, v_key_1415_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_del_object(v___x_1418_);
v___x_1421_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1415_, v_val_1416_, v_x_1393_, v_x_1394_);
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
v___y_1410_ = v___x_1422_;
goto v___jp_1409_;
}
else
{
lean_object* v___x_1424_; 
lean_dec(v_val_1416_);
lean_dec(v_key_1415_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_x_1394_);
lean_ctor_set(v___x_1418_, 0, v_x_1393_);
v___x_1424_ = v___x_1418_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_x_1393_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_x_1394_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
v___y_1410_ = v___x_1424_;
goto v___jp_1409_;
}
}
}
}
case 1:
{
lean_object* v_node_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1437_; 
v_node_1427_ = lean_ctor_get(v_v_1406_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_v_1406_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1429_ = v_v_1406_;
v_isShared_1430_ = v_isSharedCheck_1437_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_node_1427_);
lean_dec(v_v_1406_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1437_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
size_t v___x_1431_; size_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1431_ = lean_usize_shift_right(v_x_1391_, v___x_1396_);
v___x_1432_ = lean_usize_add(v_x_1392_, v___x_1397_);
v___x_1433_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1427_, v___x_1431_, v___x_1432_, v_x_1393_, v_x_1394_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1433_);
v___x_1435_ = v___x_1429_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
v___y_1410_ = v___x_1435_;
goto v___jp_1409_;
}
}
}
default: 
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_x_1393_);
lean_ctor_set(v___x_1438_, 1, v_x_1394_);
v___y_1410_ = v___x_1438_;
goto v___jp_1409_;
}
}
v___jp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_array_fset(v_xs_x27_1408_, v_j_1400_, v___y_1410_);
lean_dec(v_j_1400_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1411_);
v___x_1413_ = v___x_1404_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
else
{
lean_object* v_ks_1441_; lean_object* v_vs_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1462_; 
v_ks_1441_ = lean_ctor_get(v_x_1390_, 0);
v_vs_1442_ = lean_ctor_get(v_x_1390_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1444_ = v_x_1390_;
v_isShared_1445_ = v_isSharedCheck_1462_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_vs_1442_);
lean_inc(v_ks_1441_);
lean_dec(v_x_1390_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1462_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_ks_1441_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_vs_1442_);
v___x_1447_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v_newNode_1448_; uint8_t v___y_1450_; size_t v___x_1456_; uint8_t v___x_1457_; 
v_newNode_1448_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1447_, v_x_1393_, v_x_1394_);
v___x_1456_ = ((size_t)7ULL);
v___x_1457_ = lean_usize_dec_le(v___x_1456_, v_x_1392_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1458_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1448_);
v___x_1459_ = lean_unsigned_to_nat(4u);
v___x_1460_ = lean_nat_dec_lt(v___x_1458_, v___x_1459_);
lean_dec(v___x_1458_);
v___y_1450_ = v___x_1460_;
goto v___jp_1449_;
}
else
{
v___y_1450_ = v___x_1457_;
goto v___jp_1449_;
}
v___jp_1449_:
{
if (v___y_1450_ == 0)
{
lean_object* v_ks_1451_; lean_object* v_vs_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v_ks_1451_ = lean_ctor_get(v_newNode_1448_, 0);
lean_inc_ref(v_ks_1451_);
v_vs_1452_ = lean_ctor_get(v_newNode_1448_, 1);
lean_inc_ref(v_vs_1452_);
lean_dec_ref(v_newNode_1448_);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1455_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1392_, v_ks_1451_, v_vs_1452_, v___x_1453_, v___x_1454_);
lean_dec_ref(v_vs_1452_);
lean_dec_ref(v_ks_1451_);
return v___x_1455_;
}
else
{
return v_newNode_1448_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1463_, lean_object* v_keys_1464_, lean_object* v_vals_1465_, lean_object* v_i_1466_, lean_object* v_entries_1467_){
_start:
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = lean_array_get_size(v_keys_1464_);
v___x_1469_ = lean_nat_dec_lt(v_i_1466_, v___x_1468_);
if (v___x_1469_ == 0)
{
lean_dec(v_i_1466_);
return v_entries_1467_;
}
else
{
lean_object* v_k_1470_; lean_object* v_v_1471_; uint64_t v___x_1472_; size_t v_h_1473_; size_t v___x_1474_; lean_object* v___x_1475_; size_t v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; size_t v_h_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_k_1470_ = lean_array_fget_borrowed(v_keys_1464_, v_i_1466_);
v_v_1471_ = lean_array_fget_borrowed(v_vals_1465_, v_i_1466_);
v___x_1472_ = l_Lean_instHashableMVarId_hash(v_k_1470_);
v_h_1473_ = lean_uint64_to_usize(v___x_1472_);
v___x_1474_ = ((size_t)5ULL);
v___x_1475_ = lean_unsigned_to_nat(1u);
v___x_1476_ = ((size_t)1ULL);
v___x_1477_ = lean_usize_sub(v_depth_1463_, v___x_1476_);
v___x_1478_ = lean_usize_mul(v___x_1474_, v___x_1477_);
v_h_1479_ = lean_usize_shift_right(v_h_1473_, v___x_1478_);
v___x_1480_ = lean_nat_add(v_i_1466_, v___x_1475_);
lean_dec(v_i_1466_);
lean_inc(v_v_1471_);
lean_inc(v_k_1470_);
v___x_1481_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1467_, v_h_1479_, v_depth_1463_, v_k_1470_, v_v_1471_);
v_i_1466_ = v___x_1480_;
v_entries_1467_ = v___x_1481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1483_, lean_object* v_keys_1484_, lean_object* v_vals_1485_, lean_object* v_i_1486_, lean_object* v_entries_1487_){
_start:
{
size_t v_depth_boxed_1488_; lean_object* v_res_1489_; 
v_depth_boxed_1488_ = lean_unbox_usize(v_depth_1483_);
lean_dec(v_depth_1483_);
v_res_1489_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1488_, v_keys_1484_, v_vals_1485_, v_i_1486_, v_entries_1487_);
lean_dec_ref(v_vals_1485_);
lean_dec_ref(v_keys_1484_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_){
_start:
{
size_t v_x_838__boxed_1495_; size_t v_x_839__boxed_1496_; lean_object* v_res_1497_; 
v_x_838__boxed_1495_ = lean_unbox_usize(v_x_1491_);
lean_dec(v_x_1491_);
v_x_839__boxed_1496_ = lean_unbox_usize(v_x_1492_);
lean_dec(v_x_1492_);
v_res_1497_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1490_, v_x_838__boxed_1495_, v_x_839__boxed_1496_, v_x_1493_, v_x_1494_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
uint64_t v___x_1501_; size_t v___x_1502_; size_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1501_ = l_Lean_instHashableMVarId_hash(v_x_1499_);
v___x_1502_ = lean_uint64_to_usize(v___x_1501_);
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1498_, v___x_1502_, v___x_1503_, v_x_1499_, v_x_1500_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1505_, lean_object* v_val_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; lean_object* v_mctx_1510_; lean_object* v_cache_1511_; lean_object* v_zetaDeltaFVarIds_1512_; lean_object* v_postponed_1513_; lean_object* v_diag_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1542_; 
v___x_1509_ = lean_st_ref_take(v___y_1507_);
v_mctx_1510_ = lean_ctor_get(v___x_1509_, 0);
v_cache_1511_ = lean_ctor_get(v___x_1509_, 1);
v_zetaDeltaFVarIds_1512_ = lean_ctor_get(v___x_1509_, 2);
v_postponed_1513_ = lean_ctor_get(v___x_1509_, 3);
v_diag_1514_ = lean_ctor_get(v___x_1509_, 4);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1516_ = v___x_1509_;
v_isShared_1517_ = v_isSharedCheck_1542_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_diag_1514_);
lean_inc(v_postponed_1513_);
lean_inc(v_zetaDeltaFVarIds_1512_);
lean_inc(v_cache_1511_);
lean_inc(v_mctx_1510_);
lean_dec(v___x_1509_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1542_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v_depth_1518_; lean_object* v_levelAssignDepth_1519_; lean_object* v_lmvarCounter_1520_; lean_object* v_mvarCounter_1521_; lean_object* v_lDecls_1522_; lean_object* v_decls_1523_; lean_object* v_userNames_1524_; lean_object* v_lAssignment_1525_; lean_object* v_eAssignment_1526_; lean_object* v_dAssignment_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1541_; 
v_depth_1518_ = lean_ctor_get(v_mctx_1510_, 0);
v_levelAssignDepth_1519_ = lean_ctor_get(v_mctx_1510_, 1);
v_lmvarCounter_1520_ = lean_ctor_get(v_mctx_1510_, 2);
v_mvarCounter_1521_ = lean_ctor_get(v_mctx_1510_, 3);
v_lDecls_1522_ = lean_ctor_get(v_mctx_1510_, 4);
v_decls_1523_ = lean_ctor_get(v_mctx_1510_, 5);
v_userNames_1524_ = lean_ctor_get(v_mctx_1510_, 6);
v_lAssignment_1525_ = lean_ctor_get(v_mctx_1510_, 7);
v_eAssignment_1526_ = lean_ctor_get(v_mctx_1510_, 8);
v_dAssignment_1527_ = lean_ctor_get(v_mctx_1510_, 9);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_mctx_1510_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1529_ = v_mctx_1510_;
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
lean_inc(v_lDecls_1522_);
lean_inc(v_mvarCounter_1521_);
lean_inc(v_lmvarCounter_1520_);
lean_inc(v_levelAssignDepth_1519_);
lean_inc(v_depth_1518_);
lean_dec(v_mctx_1510_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1541_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1531_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1526_, v_mvarId_1505_, v_val_1506_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 8, v___x_1531_);
v___x_1533_ = v___x_1529_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_depth_1518_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_levelAssignDepth_1519_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_lmvarCounter_1520_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_mvarCounter_1521_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_lDecls_1522_);
lean_ctor_set(v_reuseFailAlloc_1540_, 5, v_decls_1523_);
lean_ctor_set(v_reuseFailAlloc_1540_, 6, v_userNames_1524_);
lean_ctor_set(v_reuseFailAlloc_1540_, 7, v_lAssignment_1525_);
lean_ctor_set(v_reuseFailAlloc_1540_, 8, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1540_, 9, v_dAssignment_1527_);
v___x_1533_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1535_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1533_);
v___x_1535_ = v___x_1516_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_cache_1511_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_zetaDeltaFVarIds_1512_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_postponed_1513_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_diag_1514_);
v___x_1535_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1536_ = lean_st_ref_set(v___y_1507_, v___x_1535_);
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
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = lean_box(0);
v___x_1557_ = l_Lean_Meta_synthInstance(v_a_1555_, v___x_1556_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1567_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
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
size_t v_x_1169__boxed_1630_; size_t v_x_1170__boxed_1631_; lean_object* v_res_1632_; 
v_x_1169__boxed_1630_ = lean_unbox_usize(v_x_1626_);
lean_dec(v_x_1626_);
v_x_1170__boxed_1631_ = lean_unbox_usize(v_x_1627_);
lean_dec(v_x_1627_);
v_res_1632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1624_, v_x_1625_, v_x_1169__boxed_1630_, v_x_1170__boxed_1631_, v_x_1628_, v_x_1629_);
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
lean_dec_ref_known(v___x_1669_, 1);
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
lean_dec_ref_known(v___x_1820_, 1);
v___x_1822_ = lean_box(0);
v___x_1823_ = l_Lean_Meta_synthInstance(v_a_1821_, v___x_1822_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1833_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v___x_1823_, 1);
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
v___x_1962_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
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
lean_dec_ref_known(v___x_1995_, 1);
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
lean_dec_ref_known(v___x_2031_, 1);
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
lean_dec_ref_known(v___x_2033_, 1);
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
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2130_){
_start:
{
if (lean_obj_tag(v_x_2130_) == 0)
{
uint8_t v___x_2131_; 
v___x_2131_ = 0;
return v___x_2131_;
}
else
{
lean_object* v_head_2132_; lean_object* v_tail_2133_; uint8_t v___x_2134_; 
v_head_2132_ = lean_ctor_get(v_x_2130_, 0);
v_tail_2133_ = lean_ctor_get(v_x_2130_, 1);
v___x_2134_ = l_Lean_Expr_hasMVar(v_head_2132_);
if (v___x_2134_ == 0)
{
v_x_2130_ = v_tail_2133_;
goto _start;
}
else
{
return v___x_2134_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2136_){
_start:
{
uint8_t v_res_2137_; lean_object* v_r_2138_; 
v_res_2137_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2136_);
lean_dec(v_x_2136_);
v_r_2138_ = lean_box(v_res_2137_);
return v_r_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2139_, lean_object* v_sols_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
uint8_t v___x_2146_; 
v___x_2146_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2140_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_inc(v___y_2144_);
lean_inc_ref(v___y_2143_);
lean_inc(v___y_2142_);
lean_inc_ref(v___y_2141_);
v___x_2147_ = lean_apply_6(v_test_2139_, v_sols_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, lean_box(0));
return v___x_2147_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec(v_sols_2140_);
lean_dec_ref(v_test_2139_);
v___x_2148_ = lean_box(v___x_2146_);
v___x_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
return v___x_2149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2150_, lean_object* v_sols_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2150_, v_sols_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2158_, lean_object* v_test_2159_){
_start:
{
lean_object* v___f_2160_; lean_object* v___x_2161_; 
v___f_2160_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2160_, 0, v_test_2159_);
v___x_2161_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2158_, v___f_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2162_, lean_object* v_x_2163_){
_start:
{
if (lean_obj_tag(v_x_2163_) == 0)
{
uint8_t v___x_2164_; 
lean_dec_ref(v_e_2162_);
v___x_2164_ = 0;
return v___x_2164_;
}
else
{
lean_object* v_head_2165_; lean_object* v_tail_2166_; uint8_t v___x_2167_; 
v_head_2165_ = lean_ctor_get(v_x_2163_, 0);
v_tail_2166_ = lean_ctor_get(v_x_2163_, 1);
lean_inc_ref(v_e_2162_);
v___x_2167_ = l_Lean_Expr_occurs(v_e_2162_, v_head_2165_);
if (v___x_2167_ == 0)
{
v_x_2163_ = v_tail_2166_;
goto _start;
}
else
{
lean_dec_ref(v_e_2162_);
return v___x_2167_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2169_, lean_object* v_x_2170_){
_start:
{
uint8_t v_res_2171_; lean_object* v_r_2172_; 
v_res_2171_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2169_, v_x_2170_);
lean_dec(v_x_2170_);
v_r_2172_ = lean_box(v_res_2171_);
return v_r_2172_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2173_, lean_object* v_x_2174_){
_start:
{
if (lean_obj_tag(v_x_2174_) == 0)
{
uint8_t v___x_2175_; 
v___x_2175_ = 1;
return v___x_2175_;
}
else
{
lean_object* v_head_2176_; lean_object* v_tail_2177_; uint8_t v___x_2178_; 
v_head_2176_ = lean_ctor_get(v_x_2174_, 0);
lean_inc(v_head_2176_);
v_tail_2177_ = lean_ctor_get(v_x_2174_, 1);
lean_inc(v_tail_2177_);
lean_dec_ref_known(v_x_2174_, 2);
v___x_2178_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2176_, v_sols_2173_);
if (v___x_2178_ == 0)
{
lean_dec(v_tail_2177_);
return v___x_2178_;
}
else
{
v_x_2174_ = v_tail_2177_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2180_, lean_object* v_x_2181_){
_start:
{
uint8_t v_res_2182_; lean_object* v_r_2183_; 
v_res_2182_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2180_, v_x_2181_);
lean_dec(v_sols_2180_);
v_r_2183_ = lean_box(v_res_2182_);
return v_r_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2184_, lean_object* v_sols_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
uint8_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2185_, v_use_2184_);
v___x_2192_ = lean_box(v___x_2191_);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2194_, lean_object* v_sols_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2194_, v_sols_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v_sols_2195_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2202_, lean_object* v_use_2203_){
_start:
{
lean_object* v___f_2204_; lean_object* v___x_2205_; 
v___f_2204_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2204_, 0, v_use_2203_);
v___x_2205_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2202_, v___f_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2206_){
_start:
{
lean_object* v___y_2208_; lean_object* v_toApplyRulesConfig_2209_; uint8_t v_backtracking_2210_; uint8_t v_intro_2211_; uint8_t v_constructor_2212_; uint8_t v_suggestions_2213_; uint8_t v_intro_2217_; 
v_intro_2217_ = lean_ctor_get_uint8(v_cfg_2206_, sizeof(void*)*1 + 1);
if (v_intro_2217_ == 0)
{
lean_object* v_toApplyRulesConfig_2218_; uint8_t v_backtracking_2219_; uint8_t v_constructor_2220_; uint8_t v_suggestions_2221_; 
v_toApplyRulesConfig_2218_ = lean_ctor_get(v_cfg_2206_, 0);
lean_inc_ref(v_toApplyRulesConfig_2218_);
v_backtracking_2219_ = lean_ctor_get_uint8(v_cfg_2206_, sizeof(void*)*1);
v_constructor_2220_ = lean_ctor_get_uint8(v_cfg_2206_, sizeof(void*)*1 + 2);
v_suggestions_2221_ = lean_ctor_get_uint8(v_cfg_2206_, sizeof(void*)*1 + 3);
v___y_2208_ = v_cfg_2206_;
v_toApplyRulesConfig_2209_ = v_toApplyRulesConfig_2218_;
v_backtracking_2210_ = v_backtracking_2219_;
v_intro_2211_ = v_intro_2217_;
v_constructor_2212_ = v_constructor_2220_;
v_suggestions_2213_ = v_suggestions_2221_;
goto v___jp_2207_;
}
else
{
lean_object* v_toApplyRulesConfig_2222_; uint8_t v_backtracking_2223_; uint8_t v_constructor_2224_; uint8_t v_suggestions_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2239_; 
v_toApplyRulesConfig_2222_ = lean_ctor_get(v_cfg_2206_, 0);
v_backtracking_2223_ = lean_ctor_get_uint8(v_cfg_2206_, sizeof(void*)*1);
v_constructor_2224_ = lean_ctor_get_uint8(v_cfg_2206_, sizeof(void*)*1 + 2);
v_suggestions_2225_ = lean_ctor_get_uint8(v_cfg_2206_, sizeof(void*)*1 + 3);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_cfg_2206_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2227_ = v_cfg_2206_;
v_isShared_2228_ = v_isSharedCheck_2239_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_toApplyRulesConfig_2222_);
lean_dec(v_cfg_2206_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2239_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
uint8_t v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = 0;
if (v_isShared_2228_ == 0)
{
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_toApplyRulesConfig_2222_);
lean_ctor_set_uint8(v_reuseFailAlloc_2238_, sizeof(void*)*1, v_backtracking_2223_);
lean_ctor_set_uint8(v_reuseFailAlloc_2238_, sizeof(void*)*1 + 2, v_constructor_2224_);
lean_ctor_set_uint8(v_reuseFailAlloc_2238_, sizeof(void*)*1 + 3, v_suggestions_2225_);
v___x_2231_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; lean_object* v_toApplyRulesConfig_2233_; uint8_t v_backtracking_2234_; uint8_t v_intro_2235_; uint8_t v_constructor_2236_; uint8_t v_suggestions_2237_; 
lean_ctor_set_uint8(v___x_2231_, sizeof(void*)*1 + 1, v___x_2229_);
v___x_2232_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2231_);
v_toApplyRulesConfig_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc_ref(v_toApplyRulesConfig_2233_);
v_backtracking_2234_ = lean_ctor_get_uint8(v___x_2232_, sizeof(void*)*1);
v_intro_2235_ = lean_ctor_get_uint8(v___x_2232_, sizeof(void*)*1 + 1);
v_constructor_2236_ = lean_ctor_get_uint8(v___x_2232_, sizeof(void*)*1 + 2);
v_suggestions_2237_ = lean_ctor_get_uint8(v___x_2232_, sizeof(void*)*1 + 3);
v___y_2208_ = v___x_2232_;
v_toApplyRulesConfig_2209_ = v_toApplyRulesConfig_2233_;
v_backtracking_2210_ = v_backtracking_2234_;
v_intro_2211_ = v_intro_2235_;
v_constructor_2212_ = v_constructor_2236_;
v_suggestions_2213_ = v_suggestions_2237_;
goto v___jp_2207_;
}
}
}
v___jp_2207_:
{
if (v_constructor_2212_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2209_);
return v___y_2208_;
}
else
{
uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec_ref(v___y_2208_);
v___x_2214_ = 0;
v___x_2215_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2215_, 0, v_toApplyRulesConfig_2209_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*1, v_backtracking_2210_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*1 + 1, v_intro_2211_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*1 + 2, v___x_2214_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*1 + 3, v_suggestions_2213_);
v___x_2216_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2215_);
return v___x_2216_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2240_, lean_object* v_x_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
if (lean_obj_tag(v_x_2240_) == 0)
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = l_List_reverse___redArg(v_x_2241_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
else
{
lean_object* v_head_2251_; lean_object* v_tail_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2270_; 
v_head_2251_ = lean_ctor_get(v_x_2240_, 0);
v_tail_2252_ = lean_ctor_get(v_x_2240_, 1);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_x_2240_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2254_ = v_x_2240_;
v_isShared_2255_ = v_isSharedCheck_2270_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_tail_2252_);
lean_inc(v_head_2251_);
lean_dec(v_x_2240_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2270_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; 
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
lean_inc(v___y_2243_);
lean_inc_ref(v___y_2242_);
v___x_2256_ = lean_apply_7(v_head_2251_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, lean_box(0));
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 1, v_x_2241_);
lean_ctor_set(v___x_2254_, 0, v_a_2257_);
v___x_2259_ = v___x_2254_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2257_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_x_2241_);
v___x_2259_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
v_x_2240_ = v_tail_2252_;
v_x_2241_ = v___x_2259_;
goto _start;
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_del_object(v___x_2254_);
lean_dec(v_tail_2252_);
lean_dec(v_x_2241_);
v_a_2262_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2256_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2256_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2271_, lean_object* v_x_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2271_, v_x_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2281_, lean_object* v_cfg_2282_, lean_object* v_lemmas_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
lean_inc(v___y_2289_);
lean_inc_ref(v___y_2288_);
lean_inc(v___y_2287_);
lean_inc_ref(v___y_2286_);
lean_inc(v___y_2285_);
lean_inc_ref(v___y_2284_);
v___x_2291_ = lean_apply_8(v_ctx_2281_, v_cfg_2282_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, lean_box(0));
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v___x_2293_ = lean_box(0);
v___x_2294_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2283_, v___x_2293_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2303_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2303_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2303_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2299_ = l_List_appendTR___redArg(v_a_2292_, v_a_2295_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2299_);
v___x_2301_ = v___x_2297_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
else
{
lean_dec(v_a_2292_);
return v___x_2294_;
}
}
else
{
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v_lemmas_2283_);
return v___x_2291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2304_, lean_object* v_cfg_2305_, lean_object* v_lemmas_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2304_, v_cfg_2305_, v_lemmas_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
return v_res_2314_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2315_){
_start:
{
uint8_t v___x_2316_; 
v___x_2316_ = 0;
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2317_){
_start:
{
uint8_t v_res_2318_; lean_object* v_r_2319_; 
v_res_2318_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2317_);
lean_dec(v_x_2317_);
v_r_2319_ = lean_box(v_res_2318_);
return v_r_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2320_, lean_object* v___x_2321_, lean_object* v___x_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2320_, v___x_2321_, v___x_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2337_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2337_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2337_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v_fst_2333_; lean_object* v___x_2335_; 
v_fst_2333_ = lean_ctor_get(v_a_2329_, 0);
lean_inc(v_fst_2333_);
lean_dec(v_a_2329_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v_fst_2333_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_fst_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
v_a_2338_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2328_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2328_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2346_, lean_object* v___x_2347_, lean_object* v___x_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2346_, v___x_2347_, v___x_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2369_, lean_object* v_g_2370_, lean_object* v_lemmas_2371_, lean_object* v_ctx_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v___f_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___f_2381_; lean_object* v___x_2382_; 
v___f_2378_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2378_, 0, v_ctx_2372_);
lean_closure_set(v___f_2378_, 1, v_cfg_2369_);
lean_closure_set(v___f_2378_, 2, v_lemmas_2371_);
v___x_2379_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2380_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2381_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2381_, 0, v___f_2378_);
lean_closure_set(v___f_2381_, 1, v___x_2379_);
lean_closure_set(v___f_2381_, 2, v___x_2380_);
v___x_2382_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2370_, v___f_2381_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2383_, lean_object* v_g_2384_, lean_object* v_lemmas_2385_, lean_object* v_ctx_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2383_, v_g_2384_, v_lemmas_2385_, v_ctx_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2393_, lean_object* v_lemmas_2394_, lean_object* v_ctx_2395_, lean_object* v_g_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v___x_2402_; 
lean_inc(v_g_2396_);
lean_inc_ref(v_cfg_2393_);
v___x_2402_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2393_, v_g_2396_, v_lemmas_2394_, v_ctx_2395_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_toApplyRulesConfig_2403_; lean_object* v_a_2404_; lean_object* v_toApplyConfig_2405_; uint8_t v_transparency_2406_; lean_object* v___x_2407_; 
v_toApplyRulesConfig_2403_ = lean_ctor_get(v_cfg_2393_, 0);
lean_inc_ref(v_toApplyRulesConfig_2403_);
lean_dec_ref(v_cfg_2393_);
v_a_2404_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2402_, 1);
v_toApplyConfig_2405_ = lean_ctor_get(v_toApplyRulesConfig_2403_, 1);
lean_inc_ref(v_toApplyConfig_2405_);
v_transparency_2406_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2403_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2403_);
v___x_2407_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2405_, v_transparency_2406_, v_a_2404_, v_g_2396_, v_a_2398_, v_a_2400_);
return v___x_2407_;
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_dec(v_g_2396_);
lean_dec_ref(v_cfg_2393_);
v_a_2408_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2402_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2402_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2416_, lean_object* v_lemmas_2417_, lean_object* v_ctx_2418_, lean_object* v_g_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2416_, v_lemmas_2417_, v_ctx_2418_, v_g_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2426_, lean_object* v_lemmas_2427_, lean_object* v_ctx_2428_, lean_object* v_g_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v___x_2435_; 
lean_inc(v_g_2429_);
lean_inc_ref(v_cfg_2426_);
v___x_2435_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2426_, v_g_2429_, v_lemmas_2427_, v_ctx_2428_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_toApplyRulesConfig_2436_; lean_object* v_a_2437_; lean_object* v_toApplyConfig_2438_; uint8_t v_transparency_2439_; lean_object* v___x_2440_; 
v_toApplyRulesConfig_2436_ = lean_ctor_get(v_cfg_2426_, 0);
lean_inc_ref(v_toApplyRulesConfig_2436_);
lean_dec_ref(v_cfg_2426_);
v_a_2437_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2435_, 1);
v_toApplyConfig_2438_ = lean_ctor_get(v_toApplyRulesConfig_2436_, 1);
lean_inc_ref(v_toApplyConfig_2438_);
v_transparency_2439_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2436_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2436_);
v___x_2440_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2438_, v_transparency_2439_, v_a_2437_, v_g_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
return v___x_2440_;
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec(v_g_2429_);
lean_dec_ref(v_cfg_2426_);
v_a_2441_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2435_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2435_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2449_, lean_object* v_lemmas_2450_, lean_object* v_ctx_2451_, lean_object* v_g_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2449_, v_lemmas_2450_, v_ctx_2451_, v_g_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
return v_res_2458_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2459_, lean_object* v_i_2460_, lean_object* v_k_2461_){
_start:
{
lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = lean_array_get_size(v_keys_2459_);
v___x_2463_ = lean_nat_dec_lt(v_i_2460_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_dec(v_i_2460_);
return v___x_2463_;
}
else
{
lean_object* v_k_x27_2464_; uint8_t v___x_2465_; 
v_k_x27_2464_ = lean_array_fget_borrowed(v_keys_2459_, v_i_2460_);
v___x_2465_ = l_Lean_instBEqMVarId_beq(v_k_2461_, v_k_x27_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = lean_unsigned_to_nat(1u);
v___x_2467_ = lean_nat_add(v_i_2460_, v___x_2466_);
lean_dec(v_i_2460_);
v_i_2460_ = v___x_2467_;
goto _start;
}
else
{
lean_dec(v_i_2460_);
return v___x_2465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2469_, lean_object* v_i_2470_, lean_object* v_k_2471_){
_start:
{
uint8_t v_res_2472_; lean_object* v_r_2473_; 
v_res_2472_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2469_, v_i_2470_, v_k_2471_);
lean_dec(v_k_2471_);
lean_dec_ref(v_keys_2469_);
v_r_2473_ = lean_box(v_res_2472_);
return v_r_2473_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2474_, size_t v_x_2475_, lean_object* v_x_2476_){
_start:
{
if (lean_obj_tag(v_x_2474_) == 0)
{
lean_object* v_es_2477_; lean_object* v___x_2478_; size_t v___x_2479_; size_t v___x_2480_; size_t v___x_2481_; lean_object* v_j_2482_; lean_object* v___x_2483_; 
v_es_2477_ = lean_ctor_get(v_x_2474_, 0);
v___x_2478_ = lean_box(2);
v___x_2479_ = ((size_t)5ULL);
v___x_2480_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2481_ = lean_usize_land(v_x_2475_, v___x_2480_);
v_j_2482_ = lean_usize_to_nat(v___x_2481_);
v___x_2483_ = lean_array_get_borrowed(v___x_2478_, v_es_2477_, v_j_2482_);
lean_dec(v_j_2482_);
switch(lean_obj_tag(v___x_2483_))
{
case 0:
{
lean_object* v_key_2484_; uint8_t v___x_2485_; 
v_key_2484_ = lean_ctor_get(v___x_2483_, 0);
v___x_2485_ = l_Lean_instBEqMVarId_beq(v_x_2476_, v_key_2484_);
return v___x_2485_;
}
case 1:
{
lean_object* v_node_2486_; size_t v___x_2487_; 
v_node_2486_ = lean_ctor_get(v___x_2483_, 0);
v___x_2487_ = lean_usize_shift_right(v_x_2475_, v___x_2479_);
v_x_2474_ = v_node_2486_;
v_x_2475_ = v___x_2487_;
goto _start;
}
default: 
{
uint8_t v___x_2489_; 
v___x_2489_ = 0;
return v___x_2489_;
}
}
}
else
{
lean_object* v_ks_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v_ks_2490_ = lean_ctor_get(v_x_2474_, 0);
v___x_2491_ = lean_unsigned_to_nat(0u);
v___x_2492_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2490_, v___x_2491_, v_x_2476_);
return v___x_2492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2493_, lean_object* v_x_2494_, lean_object* v_x_2495_){
_start:
{
size_t v_x_2218__boxed_2496_; uint8_t v_res_2497_; lean_object* v_r_2498_; 
v_x_2218__boxed_2496_ = lean_unbox_usize(v_x_2494_);
lean_dec(v_x_2494_);
v_res_2497_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2493_, v_x_2218__boxed_2496_, v_x_2495_);
lean_dec(v_x_2495_);
lean_dec_ref(v_x_2493_);
v_r_2498_ = lean_box(v_res_2497_);
return v_r_2498_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2499_, lean_object* v_x_2500_){
_start:
{
uint64_t v___x_2501_; size_t v___x_2502_; uint8_t v___x_2503_; 
v___x_2501_ = l_Lean_instHashableMVarId_hash(v_x_2500_);
v___x_2502_ = lean_uint64_to_usize(v___x_2501_);
v___x_2503_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2499_, v___x_2502_, v_x_2500_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2504_, lean_object* v_x_2505_){
_start:
{
uint8_t v_res_2506_; lean_object* v_r_2507_; 
v_res_2506_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2504_, v_x_2505_);
lean_dec(v_x_2505_);
lean_dec_ref(v_x_2504_);
v_r_2507_ = lean_box(v_res_2506_);
return v_r_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2511_; lean_object* v_mctx_2512_; lean_object* v_eAssignment_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2511_ = lean_st_ref_get(v___y_2509_);
v_mctx_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc_ref(v_mctx_2512_);
lean_dec(v___x_2511_);
v_eAssignment_2513_ = lean_ctor_get(v_mctx_2512_, 8);
lean_inc_ref(v_eAssignment_2513_);
lean_dec_ref(v_mctx_2512_);
v___x_2514_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2513_, v_mvarId_2508_);
lean_dec_ref(v_eAssignment_2513_);
v___x_2515_ = lean_box(v___x_2514_);
v___x_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec(v_mvarId_2517_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2521_, lean_object* v_x_2522_){
_start:
{
if (lean_obj_tag(v_x_2522_) == 0)
{
return v_x_2521_;
}
else
{
lean_object* v_head_2523_; lean_object* v_tail_2524_; lean_object* v___x_2525_; 
v_head_2523_ = lean_ctor_get(v_x_2522_, 0);
lean_inc(v_head_2523_);
v_tail_2524_ = lean_ctor_get(v_x_2522_, 1);
lean_inc(v_tail_2524_);
lean_dec_ref_known(v_x_2522_, 2);
v___x_2525_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2521_, v_head_2523_);
v_x_2521_ = v___x_2525_;
v_x_2522_ = v_tail_2524_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2527_, lean_object* v_a_2528_, uint8_t v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
if (lean_obj_tag(v_a_2530_) == 0)
{
if (lean_obj_tag(v_a_2531_) == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
lean_dec(v_a_2528_);
lean_dec_ref(v_f_2527_);
v___x_2538_ = lean_box(v_a_2529_);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
lean_ctor_set(v___x_2539_, 1, v_a_2532_);
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
return v___x_2540_;
}
else
{
lean_object* v_head_2541_; lean_object* v_tail_2542_; 
v_head_2541_ = lean_ctor_get(v_a_2531_, 0);
lean_inc(v_head_2541_);
v_tail_2542_ = lean_ctor_get(v_a_2531_, 1);
lean_inc(v_tail_2542_);
lean_dec_ref_known(v_a_2531_, 2);
v_a_2530_ = v_head_2541_;
v_a_2531_ = v_tail_2542_;
goto _start;
}
}
else
{
lean_object* v_head_2544_; lean_object* v_tail_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2588_; 
v_head_2544_ = lean_ctor_get(v_a_2530_, 0);
v_tail_2545_ = lean_ctor_get(v_a_2530_, 1);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_a_2530_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2547_ = v_a_2530_;
v_isShared_2548_ = v_isSharedCheck_2588_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_tail_2545_);
lean_inc(v_head_2544_);
lean_dec(v_a_2530_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2588_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2587_; 
v___x_2549_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2544_, v___y_2534_);
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2587_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2587_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
uint8_t v___x_2554_; 
v___x_2554_ = lean_unbox(v_a_2550_);
lean_dec(v_a_2550_);
if (v___x_2554_ == 0)
{
lean_object* v_zero_2555_; uint8_t v_isZero_2556_; 
v_zero_2555_ = lean_unsigned_to_nat(0u);
v_isZero_2556_ = lean_nat_dec_eq(v_a_2528_, v_zero_2555_);
if (v_isZero_2556_ == 1)
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
lean_del_object(v___x_2547_);
lean_dec(v_a_2528_);
lean_dec_ref(v_f_2527_);
v___x_2557_ = lean_array_push(v_a_2532_, v_head_2544_);
v___x_2558_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2557_, v_tail_2545_);
v___x_2559_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2558_, v_a_2531_);
v___x_2560_ = lean_box(v_a_2529_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
lean_ctor_set(v___x_2561_, 1, v___x_2559_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2561_);
v___x_2563_ = v___x_2552_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
else
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
lean_del_object(v___x_2552_);
lean_inc_ref(v_f_2527_);
lean_inc(v_head_2544_);
v___x_2565_ = lean_apply_1(v_f_2527_, v_head_2544_);
v___x_2566_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2565_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v_one_2568_; lean_object* v_n_2569_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
v_one_2568_ = lean_unsigned_to_nat(1u);
v_n_2569_ = lean_nat_sub(v_a_2528_, v_one_2568_);
lean_dec(v_a_2528_);
if (lean_obj_tag(v_a_2567_) == 0)
{
lean_object* v___x_2570_; 
lean_del_object(v___x_2547_);
v___x_2570_ = lean_array_push(v_a_2532_, v_head_2544_);
v_a_2528_ = v_n_2569_;
v_a_2530_ = v_tail_2545_;
v_a_2532_ = v___x_2570_;
goto _start;
}
else
{
lean_object* v_val_2572_; uint8_t v___x_2573_; lean_object* v___x_2575_; 
lean_dec(v_head_2544_);
v_val_2572_ = lean_ctor_get(v_a_2567_, 0);
lean_inc(v_val_2572_);
lean_dec_ref_known(v_a_2567_, 1);
v___x_2573_ = 1;
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 1, v_a_2531_);
lean_ctor_set(v___x_2547_, 0, v_tail_2545_);
v___x_2575_ = v___x_2547_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_tail_2545_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_a_2531_);
v___x_2575_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
v_a_2528_ = v_n_2569_;
v_a_2529_ = v___x_2573_;
v_a_2530_ = v_val_2572_;
v_a_2531_ = v___x_2575_;
goto _start;
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_del_object(v___x_2547_);
lean_dec(v_tail_2545_);
lean_dec(v_head_2544_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec(v_a_2528_);
lean_dec_ref(v_f_2527_);
v_a_2578_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2566_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2566_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
else
{
lean_del_object(v___x_2552_);
lean_del_object(v___x_2547_);
lean_dec(v_head_2544_);
v_a_2530_ = v_tail_2545_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
uint8_t v_a_2299__boxed_2600_; lean_object* v_res_2601_; 
v_a_2299__boxed_2600_ = lean_unbox(v_a_2591_);
v_res_2601_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2589_, v_a_2590_, v_a_2299__boxed_2600_, v_a_2592_, v_a_2593_, v_a_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2602_, size_t v_i_2603_, size_t v_stop_2604_, lean_object* v_b_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_a_2612_; uint8_t v___x_2616_; 
v___x_2616_ = lean_usize_dec_eq(v_i_2603_, v_stop_2604_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2620_; 
v___x_2617_ = lean_array_uget_borrowed(v_as_2602_, v_i_2603_);
v___x_2620_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2617_, v___y_2607_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; uint8_t v___x_2622_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2622_ = lean_unbox(v_a_2621_);
lean_dec(v_a_2621_);
if (v___x_2622_ == 0)
{
goto v___jp_2618_;
}
else
{
v_a_2612_ = v_b_2605_;
goto v___jp_2611_;
}
}
else
{
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2623_; uint8_t v___x_2624_; 
v_a_2623_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2624_ = lean_unbox(v_a_2623_);
lean_dec(v_a_2623_);
if (v___x_2624_ == 0)
{
v_a_2612_ = v_b_2605_;
goto v___jp_2611_;
}
else
{
goto v___jp_2618_;
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v_b_2605_);
v_a_2625_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2620_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2620_);
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
v___jp_2618_:
{
lean_object* v___x_2619_; 
lean_inc(v___x_2617_);
v___x_2619_ = lean_array_push(v_b_2605_, v___x_2617_);
v_a_2612_ = v___x_2619_;
goto v___jp_2611_;
}
}
else
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v_b_2605_);
return v___x_2633_;
}
v___jp_2611_:
{
size_t v___x_2613_; size_t v___x_2614_; 
v___x_2613_ = ((size_t)1ULL);
v___x_2614_ = lean_usize_add(v_i_2603_, v___x_2613_);
v_i_2603_ = v___x_2614_;
v_b_2605_ = v_a_2612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2634_, lean_object* v_i_2635_, lean_object* v_stop_2636_, lean_object* v_b_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
size_t v_i_boxed_2643_; size_t v_stop_boxed_2644_; lean_object* v_res_2645_; 
v_i_boxed_2643_ = lean_unbox_usize(v_i_2635_);
lean_dec(v_i_2635_);
v_stop_boxed_2644_ = lean_unbox_usize(v_stop_2636_);
lean_dec(v_stop_2636_);
v_res_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2634_, v_i_boxed_2643_, v_stop_boxed_2644_, v_b_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec_ref(v_as_2634_);
return v_res_2645_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2649_ = lean_array_to_list(v___x_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2650_, lean_object* v_goals_2651_, lean_object* v_maxIters_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
uint8_t v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2658_ = 0;
v___x_2659_ = lean_box(0);
v___x_2660_ = lean_unsigned_to_nat(0u);
v___x_2661_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2662_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2650_, v_maxIters_2652_, v___x_2658_, v_goals_2651_, v___x_2659_, v___x_2661_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2712_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2712_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2712_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v_fst_2667_; lean_object* v_snd_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2711_; 
v_fst_2667_ = lean_ctor_get(v_a_2663_, 0);
v_snd_2668_ = lean_ctor_get(v_a_2663_, 1);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_a_2663_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2670_ = v_a_2663_;
v_isShared_2671_ = v_isSharedCheck_2711_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_snd_2668_);
lean_inc(v_fst_2667_);
lean_dec(v_a_2663_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2711_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_____do__lift_2673_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2681_ = lean_array_get_size(v_snd_2668_);
v___x_2682_ = lean_nat_dec_lt(v___x_2660_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
lean_del_object(v___x_2670_);
lean_dec(v_snd_2668_);
lean_del_object(v___x_2665_);
v___x_2683_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v_fst_2667_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
else
{
uint8_t v___x_2686_; 
v___x_2686_ = lean_nat_dec_le(v___x_2681_, v___x_2681_);
if (v___x_2686_ == 0)
{
if (v___x_2682_ == 0)
{
lean_dec(v_snd_2668_);
v_____do__lift_2673_ = v___x_2661_;
goto v___jp_2672_;
}
else
{
size_t v___x_2687_; size_t v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = ((size_t)0ULL);
v___x_2688_ = lean_usize_of_nat(v___x_2681_);
v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2668_, v___x_2687_, v___x_2688_, v___x_2661_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v_snd_2668_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
v_____do__lift_2673_ = v_a_2690_;
goto v___jp_2672_;
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_del_object(v___x_2670_);
lean_dec(v_fst_2667_);
lean_del_object(v___x_2665_);
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
else
{
size_t v___x_2699_; size_t v___x_2700_; lean_object* v___x_2701_; 
v___x_2699_ = ((size_t)0ULL);
v___x_2700_ = lean_usize_of_nat(v___x_2681_);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2668_, v___x_2699_, v___x_2700_, v___x_2661_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v_snd_2668_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v_____do__lift_2673_ = v_a_2702_;
goto v___jp_2672_;
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_del_object(v___x_2670_);
lean_dec(v_fst_2667_);
lean_del_object(v___x_2665_);
v_a_2703_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2701_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2701_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
v___jp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2674_ = lean_array_to_list(v_____do__lift_2673_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v___x_2674_);
v___x_2676_ = v___x_2670_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_fst_2667_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2678_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2676_);
v___x_2678_ = v___x_2665_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_a_2713_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2662_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2662_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2721_, lean_object* v_goals_2722_, lean_object* v_maxIters_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2721_, v_goals_2722_, v_maxIters_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
return v_res_2729_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2732_ = l_Lean_stringToMessageData(v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2733_, lean_object* v_goals_2734_, lean_object* v_maxIters_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2733_, v_goals_2734_, v_maxIters_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2754_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2754_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2754_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v_fst_2746_; uint8_t v___x_2747_; 
v_fst_2746_ = lean_ctor_get(v_a_2742_, 0);
v___x_2747_ = lean_unbox(v_fst_2746_);
if (v___x_2747_ == 1)
{
lean_object* v_snd_2748_; lean_object* v___x_2750_; 
v_snd_2748_ = lean_ctor_get(v_a_2742_, 1);
lean_inc(v_snd_2748_);
lean_dec(v_a_2742_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v_snd_2748_);
v___x_2750_ = v___x_2744_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_snd_2748_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
else
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
lean_del_object(v___x_2744_);
lean_dec(v_a_2742_);
v___x_2752_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2753_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2752_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
return v___x_2753_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_a_2755_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2741_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2741_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2763_, lean_object* v_goals_2764_, lean_object* v_maxIters_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2763_, v_goals_2764_, v_maxIters_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2772_, lean_object* v_ctx_2773_, lean_object* v_cfg_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
uint8_t v_backtracking_2781_; 
v_backtracking_2781_ = lean_ctor_get_uint8(v_cfg_2774_, sizeof(void*)*1);
if (v_backtracking_2781_ == 0)
{
lean_object* v_toApplyRulesConfig_2782_; lean_object* v_toBacktrackConfig_2783_; lean_object* v_maxDepth_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_toApplyRulesConfig_2782_ = lean_ctor_get(v_cfg_2774_, 0);
v_toBacktrackConfig_2783_ = lean_ctor_get(v_toApplyRulesConfig_2782_, 0);
v_maxDepth_2784_ = lean_ctor_get(v_toBacktrackConfig_2783_, 0);
lean_inc(v_maxDepth_2784_);
v___x_2785_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2785_, 0, v_cfg_2774_);
lean_closure_set(v___x_2785_, 1, v_lemmas_2772_);
lean_closure_set(v___x_2785_, 2, v_ctx_2773_);
v___x_2786_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2785_, v_a_2775_, v_maxDepth_2784_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
return v___x_2786_;
}
else
{
lean_object* v_toApplyRulesConfig_2787_; lean_object* v_toBacktrackConfig_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_toApplyRulesConfig_2787_ = lean_ctor_get(v_cfg_2774_, 0);
v_toBacktrackConfig_2788_ = lean_ctor_get(v_toApplyRulesConfig_2787_, 0);
lean_inc_ref(v_toBacktrackConfig_2788_);
v___x_2789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2790_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2790_, 0, v_cfg_2774_);
lean_closure_set(v___x_2790_, 1, v_lemmas_2772_);
lean_closure_set(v___x_2790_, 2, v_ctx_2773_);
v___x_2791_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2788_, v___x_2789_, v___x_2790_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
return v___x_2791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2792_, lean_object* v_ctx_2793_, lean_object* v_cfg_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2792_, v_ctx_2793_, v_cfg_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2802_, v___y_2804_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v_mvarId_2809_);
return v_res_2815_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_){
_start:
{
uint8_t v___x_2819_; 
v___x_2819_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2817_, v_x_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2820_, lean_object* v_x_2821_, lean_object* v_x_2822_){
_start:
{
uint8_t v_res_2823_; lean_object* v_r_2824_; 
v_res_2823_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2820_, v_x_2821_, v_x_2822_);
lean_dec(v_x_2822_);
lean_dec_ref(v_x_2821_);
v_r_2824_ = lean_box(v_res_2823_);
return v_r_2824_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2825_, lean_object* v_x_2826_, size_t v_x_2827_, lean_object* v_x_2828_){
_start:
{
uint8_t v___x_2829_; 
v___x_2829_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2826_, v_x_2827_, v_x_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2830_, lean_object* v_x_2831_, lean_object* v_x_2832_, lean_object* v_x_2833_){
_start:
{
size_t v_x_2759__boxed_2834_; uint8_t v_res_2835_; lean_object* v_r_2836_; 
v_x_2759__boxed_2834_ = lean_unbox_usize(v_x_2832_);
lean_dec(v_x_2832_);
v_res_2835_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2830_, v_x_2831_, v_x_2759__boxed_2834_, v_x_2833_);
lean_dec(v_x_2833_);
lean_dec_ref(v_x_2831_);
v_r_2836_ = lean_box(v_res_2835_);
return v_r_2836_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2837_, lean_object* v_keys_2838_, lean_object* v_vals_2839_, lean_object* v_heq_2840_, lean_object* v_i_2841_, lean_object* v_k_2842_){
_start:
{
uint8_t v___x_2843_; 
v___x_2843_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2838_, v_i_2841_, v_k_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2844_, lean_object* v_keys_2845_, lean_object* v_vals_2846_, lean_object* v_heq_2847_, lean_object* v_i_2848_, lean_object* v_k_2849_){
_start:
{
uint8_t v_res_2850_; lean_object* v_r_2851_; 
v_res_2850_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2844_, v_keys_2845_, v_vals_2846_, v_heq_2847_, v_i_2848_, v_k_2849_);
lean_dec(v_k_2849_);
lean_dec_ref(v_vals_2846_);
lean_dec_ref(v_keys_2845_);
v_r_2851_ = lean_box(v_res_2850_);
return v_r_2851_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2854_ = l_Lean_stringToMessageData(v___x_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_x_2863_);
return v_res_2869_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2872_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2873_ = l_Lean_Name_append(v___x_2872_, v___x_2871_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2874_, lean_object* v_lemmas_2875_, lean_object* v_ctx_2876_, lean_object* v_goals_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_cfg_2883_; lean_object* v___x_2884_; 
v_cfg_2883_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2874_);
lean_inc(v_goals_2877_);
lean_inc_ref(v_cfg_2883_);
lean_inc_ref(v_ctx_2876_);
lean_inc(v_lemmas_2875_);
v___x_2884_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2875_, v_ctx_2876_, v_cfg_2883_, v_goals_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_dec_ref(v_cfg_2883_);
lean_dec(v_goals_2877_);
lean_dec_ref(v_ctx_2876_);
lean_dec(v_lemmas_2875_);
return v___x_2884_;
}
else
{
lean_object* v_a_2885_; lean_object* v___f_2886_; lean_object* v___y_2888_; lean_object* v___y_2889_; uint8_t v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; uint8_t v___y_2893_; lean_object* v___y_2894_; lean_object* v_a_2895_; lean_object* v___y_2908_; lean_object* v___y_2909_; uint8_t v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; uint8_t v___y_2913_; lean_object* v___y_2914_; lean_object* v_a_2915_; lean_object* v___y_2918_; lean_object* v___y_2919_; uint8_t v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; uint8_t v___y_2923_; lean_object* v___y_2924_; lean_object* v_a_2925_; lean_object* v___y_2935_; lean_object* v___y_2936_; uint8_t v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; uint8_t v___y_2940_; lean_object* v___y_2941_; lean_object* v_a_2942_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; uint8_t v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; uint8_t v___y_2951_; uint8_t v___y_2987_; uint8_t v___x_3040_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
v___f_2886_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_3040_ = l_Lean_Exception_isInterrupt(v_a_2885_);
if (v___x_3040_ == 0)
{
uint8_t v___x_3041_; 
v___x_3041_ = l_Lean_Exception_isRuntime(v_a_2885_);
v___y_2987_ = v___x_3041_;
goto v___jp_2986_;
}
else
{
lean_dec(v_a_2885_);
v___y_2987_ = v___x_3040_;
goto v___jp_2986_;
}
v___jp_2887_:
{
lean_object* v___x_2896_; double v___x_2897_; double v___x_2898_; double v___x_2899_; double v___x_2900_; double v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2896_ = lean_io_mono_nanos_now();
v___x_2897_ = lean_float_of_nat(v___y_2892_);
v___x_2898_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2899_ = lean_float_div(v___x_2897_, v___x_2898_);
v___x_2900_ = lean_float_of_nat(v___x_2896_);
v___x_2901_ = lean_float_div(v___x_2900_, v___x_2898_);
v___x_2902_ = lean_box_float(v___x_2899_);
v___x_2903_ = lean_box_float(v___x_2901_);
v___x_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2902_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2905_, 0, v_a_2895_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
lean_inc_ref(v___y_2888_);
lean_inc(v___y_2891_);
v___x_2906_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2891_, v___y_2893_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2894_, v___f_2886_, v___x_2905_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
return v___x_2906_;
}
v___jp_2907_:
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2916_, 0, v_a_2915_);
v___y_2888_ = v___y_2908_;
v___y_2889_ = v___y_2909_;
v___y_2890_ = v___y_2910_;
v___y_2891_ = v___y_2911_;
v___y_2892_ = v___y_2912_;
v___y_2893_ = v___y_2913_;
v___y_2894_ = v___y_2914_;
v_a_2895_ = v___x_2916_;
goto v___jp_2887_;
}
v___jp_2917_:
{
lean_object* v___x_2926_; double v___x_2927_; double v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2926_ = lean_io_get_num_heartbeats();
v___x_2927_ = lean_float_of_nat(v___y_2922_);
v___x_2928_ = lean_float_of_nat(v___x_2926_);
v___x_2929_ = lean_box_float(v___x_2927_);
v___x_2930_ = lean_box_float(v___x_2928_);
v___x_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2929_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v_a_2925_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
lean_inc_ref(v___y_2918_);
lean_inc(v___y_2921_);
v___x_2933_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2921_, v___y_2923_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2924_, v___f_2886_, v___x_2932_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
return v___x_2933_;
}
v___jp_2934_:
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_a_2942_);
v___y_2918_ = v___y_2935_;
v___y_2919_ = v___y_2936_;
v___y_2920_ = v___y_2937_;
v___y_2921_ = v___y_2938_;
v___y_2922_ = v___y_2939_;
v___y_2923_ = v___y_2940_;
v___y_2924_ = v___y_2941_;
v_a_2925_ = v___x_2943_;
goto v___jp_2917_;
}
v___jp_2944_:
{
lean_object* v___x_2952_; lean_object* v_a_2953_; lean_object* v___x_2954_; uint8_t v___x_2955_; 
v___x_2952_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2881_);
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref(v___x_2952_);
v___x_2954_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2955_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2947_, v___x_2954_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = lean_io_mono_nanos_now();
v___x_2957_ = l_Lean_MVarId_exfalso(v___y_2945_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
v___x_2959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2959_, 0, v_a_2958_);
lean_ctor_set(v___x_2959_, 1, v___y_2950_);
v___x_2960_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2875_, v_ctx_2876_, v_cfg_2883_, v___x_2959_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2960_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 1);
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
v___y_2888_ = v___y_2946_;
v___y_2889_ = v___y_2947_;
v___y_2890_ = v___y_2948_;
v___y_2891_ = v___y_2949_;
v___y_2892_ = v___x_2956_;
v___y_2893_ = v___y_2951_;
v___y_2894_ = v_a_2953_;
v_a_2895_ = v___x_2966_;
goto v___jp_2887_;
}
}
}
else
{
lean_object* v_a_2969_; 
v_a_2969_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2960_, 1);
v___y_2908_ = v___y_2946_;
v___y_2909_ = v___y_2947_;
v___y_2910_ = v___y_2948_;
v___y_2911_ = v___y_2949_;
v___y_2912_ = v___x_2956_;
v___y_2913_ = v___y_2951_;
v___y_2914_ = v_a_2953_;
v_a_2915_ = v_a_2969_;
goto v___jp_2907_;
}
}
else
{
lean_object* v_a_2970_; 
lean_dec(v___y_2950_);
lean_dec_ref(v_cfg_2883_);
lean_dec_ref(v_ctx_2876_);
lean_dec(v_lemmas_2875_);
v_a_2970_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2957_, 1);
v___y_2908_ = v___y_2946_;
v___y_2909_ = v___y_2947_;
v___y_2910_ = v___y_2948_;
v___y_2911_ = v___y_2949_;
v___y_2912_ = v___x_2956_;
v___y_2913_ = v___y_2951_;
v___y_2914_ = v_a_2953_;
v_a_2915_ = v_a_2970_;
goto v___jp_2907_;
}
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_io_get_num_heartbeats();
v___x_2972_ = l_Lean_MVarId_exfalso(v___y_2945_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___x_2972_, 1);
v___x_2974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2974_, 0, v_a_2973_);
lean_ctor_set(v___x_2974_, 1, v___y_2950_);
v___x_2975_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2875_, v_ctx_2876_, v_cfg_2883_, v___x_2974_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2975_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set_tag(v___x_2978_, 1);
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
v___y_2918_ = v___y_2946_;
v___y_2919_ = v___y_2947_;
v___y_2920_ = v___y_2948_;
v___y_2921_ = v___y_2949_;
v___y_2922_ = v___x_2971_;
v___y_2923_ = v___y_2951_;
v___y_2924_ = v_a_2953_;
v_a_2925_ = v___x_2981_;
goto v___jp_2917_;
}
}
}
else
{
lean_object* v_a_2984_; 
v_a_2984_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2975_, 1);
v___y_2935_ = v___y_2946_;
v___y_2936_ = v___y_2947_;
v___y_2937_ = v___y_2948_;
v___y_2938_ = v___y_2949_;
v___y_2939_ = v___x_2971_;
v___y_2940_ = v___y_2951_;
v___y_2941_ = v_a_2953_;
v_a_2942_ = v_a_2984_;
goto v___jp_2934_;
}
}
else
{
lean_object* v_a_2985_; 
lean_dec(v___y_2950_);
lean_dec_ref(v_cfg_2883_);
lean_dec_ref(v_ctx_2876_);
lean_dec(v_lemmas_2875_);
v_a_2985_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2985_);
lean_dec_ref_known(v___x_2972_, 1);
v___y_2935_ = v___y_2946_;
v___y_2936_ = v___y_2947_;
v___y_2937_ = v___y_2948_;
v___y_2938_ = v___y_2949_;
v___y_2939_ = v___x_2971_;
v___y_2940_ = v___y_2951_;
v___y_2941_ = v_a_2953_;
v_a_2942_ = v_a_2985_;
goto v___jp_2934_;
}
}
}
v___jp_2986_:
{
if (v___y_2987_ == 0)
{
if (lean_obj_tag(v_goals_2877_) == 1)
{
lean_object* v_tail_2988_; 
v_tail_2988_ = lean_ctor_get(v_goals_2877_, 1);
lean_inc(v_tail_2988_);
if (lean_obj_tag(v_tail_2988_) == 0)
{
lean_object* v_toApplyRulesConfig_2989_; uint8_t v_exfalso_2990_; 
v_toApplyRulesConfig_2989_ = lean_ctor_get(v_cfg_2883_, 0);
lean_inc_ref(v_toApplyRulesConfig_2989_);
v_exfalso_2990_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2989_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_2989_);
if (v_exfalso_2990_ == 1)
{
lean_object* v_options_2991_; uint8_t v_hasTrace_2992_; 
lean_dec_ref_known(v___x_2884_, 1);
v_options_2991_ = lean_ctor_get(v_a_2880_, 2);
v_hasTrace_2992_ = lean_ctor_get_uint8(v_options_2991_, sizeof(void*)*1);
if (v_hasTrace_2992_ == 0)
{
lean_object* v_head_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3011_; 
v_head_2993_ = lean_ctor_get(v_goals_2877_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_goals_2877_);
if (v_isSharedCheck_3011_ == 0)
{
lean_object* v_unused_3012_; 
v_unused_3012_ = lean_ctor_get(v_goals_2877_, 1);
lean_dec(v_unused_3012_);
v___x_2995_ = v_goals_2877_;
v_isShared_2996_ = v_isSharedCheck_3011_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_head_2993_);
lean_dec(v_goals_2877_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3011_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_MVarId_exfalso(v_head_2993_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v_a_2998_);
v___x_3000_ = v___x_2995_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2998_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_tail_2988_);
v___x_3000_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3001_; 
v___x_3001_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2875_, v_ctx_2876_, v_cfg_2883_, v___x_3000_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
return v___x_3001_;
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_del_object(v___x_2995_);
lean_dec_ref(v_cfg_2883_);
lean_dec_ref(v_ctx_2876_);
lean_dec(v_lemmas_2875_);
v_a_3003_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2997_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2997_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
else
{
lean_object* v_head_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3038_; 
v_head_3013_ = lean_ctor_get(v_goals_2877_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_goals_2877_);
if (v_isSharedCheck_3038_ == 0)
{
lean_object* v_unused_3039_; 
v_unused_3039_ = lean_ctor_get(v_goals_2877_, 1);
lean_dec(v_unused_3039_);
v___x_3015_ = v_goals_2877_;
v_isShared_3016_ = v_isSharedCheck_3038_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_head_3013_);
lean_dec(v_goals_2877_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3038_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v_inheritedTraceOptions_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v_inheritedTraceOptions_3017_ = lean_ctor_get(v_a_2880_, 13);
v___x_3018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_3019_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_3020_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_3021_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3017_, v_options_2991_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; uint8_t v___x_3023_; 
v___x_3022_ = l_Lean_trace_profiler;
v___x_3023_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2991_, v___x_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_MVarId_exfalso(v_head_3013_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3027_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v_a_3025_);
v___x_3027_ = v___x_3015_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3025_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v_tail_2988_);
v___x_3027_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3028_; 
v___x_3028_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2875_, v_ctx_2876_, v_cfg_2883_, v___x_3027_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
return v___x_3028_;
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_del_object(v___x_3015_);
lean_dec_ref(v_cfg_2883_);
lean_dec_ref(v_ctx_2876_);
lean_dec(v_lemmas_2875_);
v_a_3030_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3024_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3024_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
lean_del_object(v___x_3015_);
v___y_2945_ = v_head_3013_;
v___y_2946_ = v___x_3019_;
v___y_2947_ = v_options_2991_;
v___y_2948_ = v___x_3021_;
v___y_2949_ = v___x_3018_;
v___y_2950_ = v_tail_2988_;
v___y_2951_ = v_exfalso_2990_;
goto v___jp_2944_;
}
}
else
{
lean_del_object(v___x_3015_);
v___y_2945_ = v_head_3013_;
v___y_2946_ = v___x_3019_;
v___y_2947_ = v_options_2991_;
v___y_2948_ = v___x_3021_;
v___y_2949_ = v___x_3018_;
v___y_2950_ = v_tail_2988_;
v___y_2951_ = v_exfalso_2990_;
goto v___jp_2944_;
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2877_, 2);
lean_dec_ref(v_cfg_2883_);
lean_dec_ref(v_ctx_2876_);
lean_dec(v_lemmas_2875_);
return v___x_2884_;
}
}
else
{
lean_dec(v_tail_2988_);
lean_dec_ref_known(v_goals_2877_, 2);
lean_dec_ref(v_cfg_2883_);
lean_dec_ref(v_ctx_2876_);
lean_dec(v_lemmas_2875_);
return v___x_2884_;
}
}
else
{
lean_dec_ref(v_cfg_2883_);
lean_dec(v_goals_2877_);
lean_dec_ref(v_ctx_2876_);
lean_dec(v_lemmas_2875_);
return v___x_2884_;
}
}
else
{
lean_dec_ref(v_cfg_2883_);
lean_dec(v_goals_2877_);
lean_dec_ref(v_ctx_2876_);
lean_dec(v_lemmas_2875_);
return v___x_2884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_3042_, lean_object* v_lemmas_3043_, lean_object* v_ctx_3044_, lean_object* v_goals_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_3042_, v_lemmas_3043_, v_ctx_3044_, v_goals_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_3052_, lean_object* v_x_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
if (lean_obj_tag(v_x_3052_) == 0)
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = l_List_reverse___redArg(v_x_3053_);
v___x_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
return v___x_3060_;
}
else
{
lean_object* v_head_3061_; lean_object* v_tail_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3085_; 
v_head_3061_ = lean_ctor_get(v_x_3052_, 0);
v_tail_3062_ = lean_ctor_get(v_x_3052_, 1);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_x_3052_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3064_ = v_x_3052_;
v_isShared_3065_ = v_isSharedCheck_3085_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_tail_3062_);
lean_inc(v_head_3061_);
lean_dec(v_x_3052_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3085_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_Expr_applySymm(v_head_3061_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3069_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___x_3066_, 1);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 1, v_x_3053_);
lean_ctor_set(v___x_3064_, 0, v_a_3067_);
v___x_3069_ = v___x_3064_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3067_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v_x_3053_);
v___x_3069_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
v_x_3052_ = v_tail_3062_;
v_x_3053_ = v___x_3069_;
goto _start;
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3084_; 
lean_del_object(v___x_3064_);
v_a_3072_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3074_ = v___x_3066_;
v_isShared_3075_ = v_isSharedCheck_3084_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3066_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3084_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
uint8_t v___y_3077_; uint8_t v___x_3082_; 
v___x_3082_ = l_Lean_Exception_isInterrupt(v_a_3072_);
if (v___x_3082_ == 0)
{
uint8_t v___x_3083_; 
lean_inc(v_a_3072_);
v___x_3083_ = l_Lean_Exception_isRuntime(v_a_3072_);
v___y_3077_ = v___x_3083_;
goto v___jp_3076_;
}
else
{
v___y_3077_ = v___x_3082_;
goto v___jp_3076_;
}
v___jp_3076_:
{
if (v___y_3077_ == 0)
{
lean_del_object(v___x_3074_);
lean_dec(v_a_3072_);
v_x_3052_ = v_tail_3062_;
goto _start;
}
else
{
lean_object* v___x_3080_; 
lean_dec(v_tail_3062_);
lean_dec(v_x_3053_);
if (v_isShared_3075_ == 0)
{
v___x_3080_ = v___x_3074_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3072_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_3086_, lean_object* v_x_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_3086_, v_x_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_3094_, lean_object* v_hyps_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
if (v_symm_3094_ == 0)
{
lean_object* v___x_3101_; 
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v_hyps_3095_);
return v___x_3101_;
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_box(0);
lean_inc(v_hyps_3095_);
v___x_3103_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_3095_, v___x_3102_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3112_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3112_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3112_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3108_ = l_List_appendTR___redArg(v_hyps_3095_, v_a_3104_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v___x_3108_);
v___x_3110_ = v___x_3106_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
else
{
lean_dec(v_hyps_3095_);
return v___x_3103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3113_, lean_object* v_hyps_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
uint8_t v_symm_boxed_3120_; lean_object* v_res_3121_; 
v_symm_boxed_3120_ = lean_unbox(v_symm_3113_);
v_res_3121_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3120_, v_hyps_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_);
lean_dec(v_a_3118_);
lean_dec_ref(v_a_3117_);
lean_dec(v_a_3116_);
lean_dec_ref(v_a_3115_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3122_, size_t v_sz_3123_, size_t v_i_3124_, lean_object* v_b_3125_){
_start:
{
uint8_t v___x_3127_; 
v___x_3127_ = lean_usize_dec_lt(v_i_3124_, v_sz_3123_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v_b_3125_);
return v___x_3128_;
}
else
{
lean_object* v_snd_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3147_; 
v_snd_3129_ = lean_ctor_get(v_b_3125_, 1);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_b_3125_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; 
v_unused_3148_ = lean_ctor_get(v_b_3125_, 0);
lean_dec(v_unused_3148_);
v___x_3131_ = v_b_3125_;
v_isShared_3132_ = v_isSharedCheck_3147_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_snd_3129_);
lean_dec(v_b_3125_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3147_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3133_; lean_object* v_a_3135_; lean_object* v_a_3142_; 
v___x_3133_ = lean_box(0);
v_a_3142_ = lean_array_uget_borrowed(v_as_3122_, v_i_3124_);
if (lean_obj_tag(v_a_3142_) == 0)
{
v_a_3135_ = v_snd_3129_;
goto v___jp_3134_;
}
else
{
lean_object* v_val_3143_; uint8_t v___x_3144_; 
v_val_3143_ = lean_ctor_get(v_a_3142_, 0);
v___x_3144_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3143_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_inc(v_val_3143_);
v___x_3145_ = l_Lean_LocalDecl_toExpr(v_val_3143_);
v___x_3146_ = lean_array_push(v_snd_3129_, v___x_3145_);
v_a_3135_ = v___x_3146_;
goto v___jp_3134_;
}
else
{
v_a_3135_ = v_snd_3129_;
goto v___jp_3134_;
}
}
v___jp_3134_:
{
lean_object* v___x_3137_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 1, v_a_3135_);
lean_ctor_set(v___x_3131_, 0, v___x_3133_);
v___x_3137_ = v___x_3131_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_a_3135_);
v___x_3137_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
size_t v___x_3138_; size_t v___x_3139_; 
v___x_3138_ = ((size_t)1ULL);
v___x_3139_ = lean_usize_add(v_i_3124_, v___x_3138_);
v_i_3124_ = v___x_3139_;
v_b_3125_ = v___x_3137_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3149_, lean_object* v_sz_3150_, lean_object* v_i_3151_, lean_object* v_b_3152_, lean_object* v___y_3153_){
_start:
{
size_t v_sz_boxed_3154_; size_t v_i_boxed_3155_; lean_object* v_res_3156_; 
v_sz_boxed_3154_ = lean_unbox_usize(v_sz_3150_);
lean_dec(v_sz_3150_);
v_i_boxed_3155_ = lean_unbox_usize(v_i_3151_);
lean_dec(v_i_3151_);
v_res_3156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3149_, v_sz_boxed_3154_, v_i_boxed_3155_, v_b_3152_);
lean_dec_ref(v_as_3149_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3157_, size_t v_sz_3158_, size_t v_i_3159_, lean_object* v_b_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
uint8_t v___x_3168_; 
v___x_3168_ = lean_usize_dec_lt(v_i_3159_, v_sz_3158_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; 
v___x_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3169_, 0, v_b_3160_);
return v___x_3169_;
}
else
{
lean_object* v_snd_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3188_; 
v_snd_3170_ = lean_ctor_get(v_b_3160_, 1);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_b_3160_);
if (v_isSharedCheck_3188_ == 0)
{
lean_object* v_unused_3189_; 
v_unused_3189_ = lean_ctor_get(v_b_3160_, 0);
lean_dec(v_unused_3189_);
v___x_3172_ = v_b_3160_;
v_isShared_3173_ = v_isSharedCheck_3188_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_snd_3170_);
lean_dec(v_b_3160_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3188_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v_a_3176_; lean_object* v_a_3183_; 
v___x_3174_ = lean_box(0);
v_a_3183_ = lean_array_uget_borrowed(v_as_3157_, v_i_3159_);
if (lean_obj_tag(v_a_3183_) == 0)
{
v_a_3176_ = v_snd_3170_;
goto v___jp_3175_;
}
else
{
lean_object* v_val_3184_; uint8_t v___x_3185_; 
v_val_3184_ = lean_ctor_get(v_a_3183_, 0);
v___x_3185_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3184_);
if (v___x_3185_ == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_inc(v_val_3184_);
v___x_3186_ = l_Lean_LocalDecl_toExpr(v_val_3184_);
v___x_3187_ = lean_array_push(v_snd_3170_, v___x_3186_);
v_a_3176_ = v___x_3187_;
goto v___jp_3175_;
}
else
{
v_a_3176_ = v_snd_3170_;
goto v___jp_3175_;
}
}
v___jp_3175_:
{
lean_object* v___x_3178_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 1, v_a_3176_);
lean_ctor_set(v___x_3172_, 0, v___x_3174_);
v___x_3178_ = v___x_3172_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_a_3176_);
v___x_3178_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
size_t v___x_3179_; size_t v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = ((size_t)1ULL);
v___x_3180_ = lean_usize_add(v_i_3159_, v___x_3179_);
v___x_3181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3157_, v_sz_3158_, v___x_3180_, v___x_3178_);
return v___x_3181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3190_, lean_object* v_sz_3191_, lean_object* v_i_3192_, lean_object* v_b_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
size_t v_sz_boxed_3201_; size_t v_i_boxed_3202_; lean_object* v_res_3203_; 
v_sz_boxed_3201_ = lean_unbox_usize(v_sz_3191_);
lean_dec(v_sz_3191_);
v_i_boxed_3202_ = lean_unbox_usize(v_i_3192_);
lean_dec(v_i_3192_);
v_res_3203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3190_, v_sz_boxed_3201_, v_i_boxed_3202_, v_b_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec_ref(v_as_3190_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3204_, size_t v_sz_3205_, size_t v_i_3206_, lean_object* v_b_3207_){
_start:
{
uint8_t v___x_3209_; 
v___x_3209_ = lean_usize_dec_lt(v_i_3206_, v_sz_3205_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; 
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_b_3207_);
return v___x_3210_;
}
else
{
lean_object* v_snd_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3229_; 
v_snd_3211_ = lean_ctor_get(v_b_3207_, 1);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_b_3207_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v_b_3207_, 0);
lean_dec(v_unused_3230_);
v___x_3213_ = v_b_3207_;
v_isShared_3214_ = v_isSharedCheck_3229_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_snd_3211_);
lean_dec(v_b_3207_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3229_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3215_; lean_object* v_a_3217_; lean_object* v_a_3224_; 
v___x_3215_ = lean_box(0);
v_a_3224_ = lean_array_uget_borrowed(v_as_3204_, v_i_3206_);
if (lean_obj_tag(v_a_3224_) == 0)
{
v_a_3217_ = v_snd_3211_;
goto v___jp_3216_;
}
else
{
lean_object* v_val_3225_; uint8_t v___x_3226_; 
v_val_3225_ = lean_ctor_get(v_a_3224_, 0);
v___x_3226_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
lean_inc(v_val_3225_);
v___x_3227_ = l_Lean_LocalDecl_toExpr(v_val_3225_);
v___x_3228_ = lean_array_push(v_snd_3211_, v___x_3227_);
v_a_3217_ = v___x_3228_;
goto v___jp_3216_;
}
else
{
v_a_3217_ = v_snd_3211_;
goto v___jp_3216_;
}
}
v___jp_3216_:
{
lean_object* v___x_3219_; 
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 1, v_a_3217_);
lean_ctor_set(v___x_3213_, 0, v___x_3215_);
v___x_3219_ = v___x_3213_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v_a_3217_);
v___x_3219_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
size_t v___x_3220_; size_t v___x_3221_; 
v___x_3220_ = ((size_t)1ULL);
v___x_3221_ = lean_usize_add(v_i_3206_, v___x_3220_);
v_i_3206_ = v___x_3221_;
v_b_3207_ = v___x_3219_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3231_, lean_object* v_sz_3232_, lean_object* v_i_3233_, lean_object* v_b_3234_, lean_object* v___y_3235_){
_start:
{
size_t v_sz_boxed_3236_; size_t v_i_boxed_3237_; lean_object* v_res_3238_; 
v_sz_boxed_3236_ = lean_unbox_usize(v_sz_3232_);
lean_dec(v_sz_3232_);
v_i_boxed_3237_ = lean_unbox_usize(v_i_3233_);
lean_dec(v_i_3233_);
v_res_3238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3231_, v_sz_boxed_3236_, v_i_boxed_3237_, v_b_3234_);
lean_dec_ref(v_as_3231_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3239_, size_t v_sz_3240_, size_t v_i_3241_, lean_object* v_b_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
uint8_t v___x_3250_; 
v___x_3250_ = lean_usize_dec_lt(v_i_3241_, v_sz_3240_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; 
v___x_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3251_, 0, v_b_3242_);
return v___x_3251_;
}
else
{
lean_object* v_snd_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3270_; 
v_snd_3252_ = lean_ctor_get(v_b_3242_, 1);
v_isSharedCheck_3270_ = !lean_is_exclusive(v_b_3242_);
if (v_isSharedCheck_3270_ == 0)
{
lean_object* v_unused_3271_; 
v_unused_3271_ = lean_ctor_get(v_b_3242_, 0);
lean_dec(v_unused_3271_);
v___x_3254_ = v_b_3242_;
v_isShared_3255_ = v_isSharedCheck_3270_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_snd_3252_);
lean_dec(v_b_3242_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3270_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v_a_3258_; lean_object* v_a_3265_; 
v___x_3256_ = lean_box(0);
v_a_3265_ = lean_array_uget_borrowed(v_as_3239_, v_i_3241_);
if (lean_obj_tag(v_a_3265_) == 0)
{
v_a_3258_ = v_snd_3252_;
goto v___jp_3257_;
}
else
{
lean_object* v_val_3266_; uint8_t v___x_3267_; 
v_val_3266_ = lean_ctor_get(v_a_3265_, 0);
v___x_3267_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
lean_inc(v_val_3266_);
v___x_3268_ = l_Lean_LocalDecl_toExpr(v_val_3266_);
v___x_3269_ = lean_array_push(v_snd_3252_, v___x_3268_);
v_a_3258_ = v___x_3269_;
goto v___jp_3257_;
}
else
{
v_a_3258_ = v_snd_3252_;
goto v___jp_3257_;
}
}
v___jp_3257_:
{
lean_object* v___x_3260_; 
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 1, v_a_3258_);
lean_ctor_set(v___x_3254_, 0, v___x_3256_);
v___x_3260_ = v___x_3254_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_a_3258_);
v___x_3260_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
size_t v___x_3261_; size_t v___x_3262_; lean_object* v___x_3263_; 
v___x_3261_ = ((size_t)1ULL);
v___x_3262_ = lean_usize_add(v_i_3241_, v___x_3261_);
v___x_3263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3239_, v_sz_3240_, v___x_3262_, v___x_3260_);
return v___x_3263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3272_, lean_object* v_sz_3273_, lean_object* v_i_3274_, lean_object* v_b_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
size_t v_sz_boxed_3283_; size_t v_i_boxed_3284_; lean_object* v_res_3285_; 
v_sz_boxed_3283_ = lean_unbox_usize(v_sz_3273_);
lean_dec(v_sz_3273_);
v_i_boxed_3284_ = lean_unbox_usize(v_i_3274_);
lean_dec(v_i_3274_);
v_res_3285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3272_, v_sz_boxed_3283_, v_i_boxed_3284_, v_b_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_as_3272_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3286_, lean_object* v_n_3287_, lean_object* v_b_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
if (lean_obj_tag(v_n_3287_) == 0)
{
lean_object* v_cs_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; size_t v_sz_3299_; size_t v___x_3300_; lean_object* v___x_3301_; 
v_cs_3296_ = lean_ctor_get(v_n_3287_, 0);
v___x_3297_ = lean_box(0);
v___x_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
lean_ctor_set(v___x_3298_, 1, v_b_3288_);
v_sz_3299_ = lean_array_size(v_cs_3296_);
v___x_3300_ = ((size_t)0ULL);
v___x_3301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3286_, v_cs_3296_, v_sz_3299_, v___x_3300_, v___x_3298_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3316_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3316_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3316_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v_fst_3306_; 
v_fst_3306_ = lean_ctor_get(v_a_3302_, 0);
if (lean_obj_tag(v_fst_3306_) == 0)
{
lean_object* v_snd_3307_; lean_object* v___x_3308_; lean_object* v___x_3310_; 
v_snd_3307_ = lean_ctor_get(v_a_3302_, 1);
lean_inc(v_snd_3307_);
lean_dec(v_a_3302_);
v___x_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3308_, 0, v_snd_3307_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v___x_3308_);
v___x_3310_ = v___x_3304_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
else
{
lean_object* v_val_3312_; lean_object* v___x_3314_; 
lean_inc_ref(v_fst_3306_);
lean_dec(v_a_3302_);
v_val_3312_ = lean_ctor_get(v_fst_3306_, 0);
lean_inc(v_val_3312_);
lean_dec_ref_known(v_fst_3306_, 1);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v_val_3312_);
v___x_3314_ = v___x_3304_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_val_3312_);
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
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
v_a_3317_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3301_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3301_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v_vs_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; size_t v_sz_3328_; size_t v___x_3329_; lean_object* v___x_3330_; 
v_vs_3325_ = lean_ctor_get(v_n_3287_, 0);
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
lean_ctor_set(v___x_3327_, 1, v_b_3288_);
v_sz_3328_ = lean_array_size(v_vs_3325_);
v___x_3329_ = ((size_t)0ULL);
v___x_3330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3325_, v_sz_3328_, v___x_3329_, v___x_3327_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3345_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3333_ = v___x_3330_;
v_isShared_3334_ = v_isSharedCheck_3345_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3330_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3345_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v_fst_3335_; 
v_fst_3335_ = lean_ctor_get(v_a_3331_, 0);
if (lean_obj_tag(v_fst_3335_) == 0)
{
lean_object* v_snd_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
v_snd_3336_ = lean_ctor_get(v_a_3331_, 1);
lean_inc(v_snd_3336_);
lean_dec(v_a_3331_);
v___x_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3337_, 0, v_snd_3336_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v___x_3337_);
v___x_3339_ = v___x_3333_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
else
{
lean_object* v_val_3341_; lean_object* v___x_3343_; 
lean_inc_ref(v_fst_3335_);
lean_dec(v_a_3331_);
v_val_3341_ = lean_ctor_get(v_fst_3335_, 0);
lean_inc(v_val_3341_);
lean_dec_ref_known(v_fst_3335_, 1);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v_val_3341_);
v___x_3343_ = v___x_3333_;
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
v_a_3346_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3330_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3330_);
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
lean_dec_ref_known(v_a_3374_, 1);
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
lean_dec_ref(v_n_3420_);
lean_dec_ref(v_init_3419_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3430_, lean_object* v_init_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v_root_3439_; lean_object* v_tail_3440_; lean_object* v___x_3441_; 
v_root_3439_ = lean_ctor_get(v_t_3430_, 0);
v_tail_3440_ = lean_ctor_get(v_t_3430_, 1);
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
v_a_3446_ = lean_ctor_get(v_a_3442_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v_a_3442_, 1);
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
lean_dec_ref_known(v_a_3442_, 1);
v___x_3451_ = lean_box(0);
v___x_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
lean_ctor_set(v___x_3452_, 1, v_a_3450_);
v_sz_3453_ = lean_array_size(v_tail_3440_);
v___x_3454_ = ((size_t)0ULL);
v___x_3455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3440_, v_sz_3453_, v___x_3454_, v___x_3452_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
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
lean_dec_ref_known(v_fst_3460_, 1);
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
lean_dec_ref(v_t_3487_);
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
lean_dec_ref_known(v___x_3527_, 1);
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
lean_dec_ref_known(v___x_3718_, 1);
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
lean_dec_ref_known(v___x_3755_, 1);
v___x_3757_ = lean_box(0);
v___x_3758_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3743_, v___x_3757_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_toApplyRulesConfig_3759_; lean_object* v_a_3760_; uint8_t v_symm_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_toApplyRulesConfig_3759_ = lean_ctor_get(v_cfg_3746_, 0);
v_a_3760_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3758_, 1);
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
lean_dec_ref_known(v___x_3830_, 1);
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
v___y_3950_ = v___y_3957_;
v___y_3951_ = v___y_3960_;
goto v___jp_3949_;
}
else
{
if (v_star_3940_ == 0)
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3957_);
v___x_3962_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3963_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3962_, v___y_3959_, v___y_3958_, v___y_3956_, v___y_3955_);
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
v___y_3950_ = v___y_3957_;
v___y_3951_ = v___y_3960_;
goto v___jp_3949_;
}
}
}
else
{
v___y_3950_ = v___y_3957_;
v___y_3951_ = v___y_3960_;
goto v___jp_3949_;
}
}
v___jp_3975_:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = lean_array_to_list(v___y_3982_);
lean_inc(v___y_3981_);
v___x_3984_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3983_, v___y_3981_);
if (v_noDefaults_3939_ == 0)
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3985_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3941_, v___y_3981_);
v___x_3986_ = l_List_appendTR___redArg(v___x_3985_, v___x_3984_);
v___x_3987_ = l_List_appendTR___redArg(v___x_3986_, v___y_3978_);
v___y_3955_ = v___y_3977_;
v___y_3956_ = v___y_3976_;
v___y_3957_ = v___f_3974_;
v___y_3958_ = v___y_3979_;
v___y_3959_ = v___y_3980_;
v___y_3960_ = v___x_3987_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
lean_dec(v___y_3978_);
v___x_3988_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3941_, v___y_3981_);
v___x_3989_ = l_List_appendTR___redArg(v___x_3988_, v___x_3984_);
v___y_3955_ = v___y_3977_;
v___y_3956_ = v___y_3976_;
v___y_3957_ = v___f_3974_;
v___y_3958_ = v___y_3979_;
v___y_3959_ = v___y_3980_;
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
lean_dec_ref_known(v___x_4013_, 1);
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
v___y_3977_ = v___y_3994_;
v___y_3978_ = v___x_4035_;
v___y_3979_ = v___y_3992_;
v___y_3980_ = v___y_3991_;
v___y_3981_ = v___x_4022_;
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
v___y_3977_ = v___y_3994_;
v___y_3978_ = v___x_4035_;
v___y_3979_ = v___y_3992_;
v___y_3980_ = v___y_3991_;
v___y_3981_ = v___x_4022_;
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
v___y_3977_ = v___y_3994_;
v___y_3978_ = v___x_4035_;
v___y_3979_ = v___y_3992_;
v___y_3980_ = v___y_3991_;
v___y_3981_ = v___x_4022_;
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
v___y_3977_ = v___y_3994_;
v___y_3978_ = v___x_4035_;
v___y_3979_ = v___y_3992_;
v___y_3980_ = v___y_3991_;
v___y_3981_ = v___x_4022_;
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
